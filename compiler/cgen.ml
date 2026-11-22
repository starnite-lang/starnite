(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Passes 10, 13 (naive) and 16: monomorphize, insert counts, emit C11 (sections 9, 11).
   Milestone 1 counting is naive (section 22.1): every local owns one reference and is
   released when its scope ends; every copy into an owning position is a dup. *)

open Syntax
open Types

exception Unsupported = Syntax.Unsupported

let unsupported l fmt = Printf.ksprintf (fun m -> raise (Unsupported (m, l))) fmt

type layout = LInline | LBoxed

type st = {
  prog : tprog;
  fwd : Buffer.t;            (* forward typedefs *)
  typedefs : Buffer.t;       (* inline type definitions, in dependency order *)
  boxed_bodies : Buffer.t;   (* boxed type definitions *)
  protos : Buffer.t;
  helpers : Buffer.t;
  funcs : Buffer.t;
  defined : (string, unit) Hashtbl.t;
  pending_boxed : (ty * string) Queue.t;
  instances : (string, unit) Hashtbl.t;
  queue : (string * string * ty list) Queue.t;
  strlits : (string, string) Hashtbl.t;
  errtypes : (string, int * ty) Hashtbl.t;
  layouts : (string, layout) Hashtbl.t;
  debug : bool;
  mutable counter : int;
}

let fresh st prefix = st.counter <- st.counter + 1; Printf.sprintf "%s%d" prefix st.counter

let pr buf fmt = Printf.bprintf buf fmt

(* ---------- names ---------- *)

(* A name chosen in the program, as part of a C name. The C names join their parts with
   an underscore, so a name that has one, or that reads like a part of the scheme (Arr,
   Any, E, Tup2, anything starting with Fn or with a lower-case letter, ...), is spelled out instead: Zq, then the name with Z written ZZ and
   an underscore Zu. A plain name never starts with Z, so the two kinds cannot meet,
   and two different types or traits always get different C names. *)
let mangle_name n =
  let reserved = [ "Int"; "I8"; "I16"; "I32"; "I64"; "U8"; "U16"; "U32"; "U64"; "Float"; "F32"; "Bool"; "Char"; "Unit";
                   "Str"; "Dur"; "Bytes"; "Arr"; "Fn"; "Err"; "Any"; "E" ] in
  let is_tuple_word =
    String.length n > 3 && String.sub n 0 3 = "Tup"
    && String.for_all (fun c -> c >= '0' && c <= '9') (String.sub n 3 (String.length n - 3))
  in
  let plain =
    n <> "" && n.[0] <> 'Z'
    (* Fn followed by a digest is how a function type is named *)
    && not (String.length n >= 2 && String.sub n 0 2 = "Fn")
    (* a C name is stn_ and the name, and the runtime's own names (stn_header, stn_alloc, ...)
       start with a lower-case letter after it *)
    && not (n.[0] >= 'a' && n.[0] <= 'z')
    && String.for_all (fun c -> (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')) n
    && (not (List.mem n reserved)) && not is_tuple_word
  in
  if plain then n
  else
    "Zq" ^ String.concat "" (List.map (function 'Z' -> "ZZ" | '_' -> "Zu" | c -> String.make 1 c) (List.init (String.length n) (String.get n)))

(* The C name of a type. Every function type is one C type, so [mangle] gives them all the
   name Fn. [mangle_eff] keeps them apart: where two types must stay different by more
   than their C type, because an impl is chosen by them (the trait arguments of a trait
   value, the type an impl is for, the type arguments of an instance), a function type
   goes into the name whole, through a digest of its parameters with their modes, its
   result and its effects as a set. A trait value's own name always uses it for its trait
   arguments. *)
let rec mangle_with (fine : bool) t =
  let go = mangle_with fine in
  match repr t with
  | TInt k -> ikind_name k
  | TFloat -> "Float" | TF32 -> "F32" | TBool -> "Bool" | TChar -> "Char" | TUnit | TNever -> "Unit"
  | TStr -> "Str" | TDur -> "Dur" | TBytes -> "Bytes"
  | TArray t -> "Arr_" ^ go t ^ "_E"
  | TTuple ts -> Printf.sprintf "Tup%d_%s_E" (List.length ts) (String.concat "_" (List.map go ts))
  | TNamed (n, []) -> mangle_name n
  | TNamed (n, ts) -> mangle_name n ^ "_" ^ String.concat "_" (List.map go ts) ^ "_E"
  | TFn f -> if fine then "Fn" ^ fn_digest f else "Fn"
  | TErr _ -> "Err"
  | TAny (n, ts) -> "Any_" ^ mangle_name n ^ "_" ^ String.concat "_" (List.map (mangle_with true) ts) ^ "_E"
  | TParam p -> failwith ("cgen: unsubstituted type parameter " ^ p)
  | TVar _ -> failwith "cgen: unresolved type variable"

and fn_digest (f : fnty) : string =
  let errs = List.sort compare (List.map (mangle_with true) f.feff.errs) in
  let mode = function MMut -> "mut " | MTake -> "take " | MBorrow -> "" in
  let s =
    Printf.sprintf "(%s)->%s!%b,%b,%s"
      (String.concat "," (List.map (fun (m, t) -> mode m ^ mangle_with true t) f.fps))
      (mangle_with true f.fret) f.feff.io f.feff.poly (String.concat "," errs)
  in
  String.sub (Digest.to_hex (Digest.string s)) 0 16

let mangle t = mangle_with false t
let mangle_eff t = mangle_with true t

let c_ident s =
  String.map (fun ch -> if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch = '_' then ch else '_') s

(* the member of a method table that holds a trait method: prefixed, since a bare method
   name can be a macro in the C headers (isnan, signbit, ...) *)
let vt_member m = "m_" ^ c_ident m

let c_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun ch ->
      match ch with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\t' -> Buffer.add_string b "\\t"
      | '\r' -> Buffer.add_string b "\\r"
      | ch when Char.code ch < 0x20 || Char.code ch >= 0x7F -> Buffer.add_string b (Printf.sprintf "\\%03o" (Char.code ch))
      | ch -> Buffer.add_char b ch)
    s;
  Buffer.add_char b '"';
  (* "??" trigraph sequences cannot occur: '?' is escaped below *)
  let r = Buffer.contents b in
  String.concat "\\?" (String.split_on_char '?' r)

(* ---------- types ---------- *)

let decl st n = Hashtbl.find st.prog.decls n

let decl_subst st n args = let d = decl st n in (d, List.combine d.dparams args)

let variants st t =
  match repr t with
  | TNamed (n, args) -> (
      let d, s = decl_subst st n args in
      match d.dbody with
      | DData vs -> List.map (fun v -> (v, List.map (fun f -> (f.fname_, subst s f.fty)) v.vfields)) vs
      | _ -> [])
  | _ -> []

let struct_fields st t =
  match repr t with
  | TNamed (n, args) -> (
      let d, s = decl_subst st n args in
      match d.dbody with DStruct fs -> List.map (fun f -> (f.fname_, subst s f.fty)) fs | _ -> [])
  | _ -> []

let is_data st t = match repr t with TNamed (n, _) -> (match (decl st n).dbody with DData _ -> true | _ -> false) | _ -> false
let is_struct st t = match repr t with TNamed (n, _) -> (match (decl st n).dbody with DStruct _ -> true | _ -> false) | _ -> false

(* By-value containment edges used for the recursion test of section 3.3. *)
let rec by_value_children st t =
  match repr t with
  | TTuple ts -> ts
  | TNamed _ when is_struct st t -> List.map snd (struct_fields st t)
  | TNamed _ when is_data st t -> List.concat_map (fun (_, fs) -> List.map snd fs) (variants st t)
  | _ -> []

let rec size_of st t =
  match repr t with
  | TInt k -> ikind_bits k / 8
  | TFloat | TDur | TBytes -> 8
  | TF32 | TChar -> 4
  | TBool | TUnit | TNever -> 1
  | TStr | TArray _ | TFn _ -> 8
  | TErr _ | TAny _ -> 16
  | TTuple ts -> List.fold_left (fun a t -> a + max 8 (size_of st t)) 0 ts
  | TNamed _ when is_struct st t -> List.fold_left (fun a (_, t) -> a + max 1 (size_of st t)) 0 (struct_fields st t)
  | TNamed _ when is_data st t -> if layout st t = LBoxed then 8 else 1 + payload_size st t
  | _ -> 8

and payload_size st t =
  List.fold_left (fun a (_, fs) -> max a (List.fold_left (fun a (_, t) -> a + max 1 (size_of st t)) 0 fs)) 0 (variants st t)

and layout st t : layout =
  let key = mangle t in
  match Hashtbl.find_opt st.layouts key with
  | Some l -> l
  | None ->
      (* provisional: assume boxed while deciding, so recursion terminates *)
      Hashtbl.replace st.layouts key LBoxed;
      let rec reaches seen u =
        let k = mangle u in
        if List.mem k seen then false
        else
          List.exists (fun c -> mangle c = key || reaches (k :: seen) c) (by_value_children st u)
      in
      let recursive = reaches [] t in
      let l =
        if recursive then LBoxed
        else if payload_size st t > 16 then LBoxed
        else LInline
      in
      Hashtbl.replace st.layouts key l;
      l

let sig_can_fail_sg (sg : fsig) =
  sg.seff.errs <> [] || List.exists (fun (_, _, t, _) -> match repr t with TFn f -> f.feff.poly | _ -> false) sg.sparams

let rec needs_rc st t =
  match repr t with
  | TStr | TArray _ | TFn _ | TErr _ | TAny _ -> true
  | TTuple ts -> List.exists (needs_rc st) ts
  | TNamed _ when is_struct st t -> List.exists (fun (_, t) -> needs_rc st t) (struct_fields st t)
  | TNamed _ when is_data st t -> layout st t = LBoxed || List.exists (fun (_, fs) -> List.exists (fun (_, t) -> needs_rc st t) fs) (variants st t)
  | _ -> false

let rec cty st t : string =
  match repr t with
  | TInt IInt | TInt I64 -> "int64_t"
  | TInt I8 -> "int8_t" | TInt I16 -> "int16_t" | TInt I32 -> "int32_t"
  | TInt U8 -> "uint8_t" | TInt U16 -> "uint16_t" | TInt U32 -> "uint32_t" | TInt U64 -> "uint64_t"
  | TFloat -> "double" | TF32 -> "float" | TBool -> "uint8_t" | TChar -> "uint32_t"
  | TUnit | TNever -> "StnUnit"
  | TStr -> "StnStr"
  | TDur | TBytes -> "int64_t"
  | TArray _ -> "StnArray*"
  | TFn _ -> "StnClosure*"
  | TErr _ -> "StnError"
  | TTuple _ | TNamed _ | TAny _ -> ensure_type st t; "stn_" ^ mangle t
  | TParam p -> failwith ("cgen: type parameter " ^ p)
  | TVar _ -> failwith "cgen: type variable"

and fname f = "f_" ^ c_ident f

and ensure_type st t =
  let m = mangle t in
  if not (Hashtbl.mem st.defined m) then begin
    Hashtbl.replace st.defined m ();
    match repr t with
    | TTuple ts ->
        let fields = List.mapi (fun i t -> Printf.sprintf "%s f%d;" (cty st t) i) ts in
        pr st.typedefs "typedef struct { %s } stn_%s;\n" (String.concat " " fields) m;
        emit_helpers st t
    | TAny (tr, ta) ->
        (* two words: the counted box and the method table (section 3.4) *)
        let info = Hashtbl.find st.prog.traits tr in
        let s = List.combine info.trparams ta in
        (* the two-word type comes first: a method's types may refer back to it *)
        pr st.typedefs "typedef struct StnVt_%s StnVt_%s;\ntypedef struct { StnAnyBox* box; const StnVt_%s* vt; } stn_%s;\n" m m m m;
        let members =
          List.map
            (fun (m, (sg : fsig)) ->
              let ps = List.map (fun (md, _, pt, _) -> match md with MMut -> cty st (subst s pt) ^ "*" | _ -> cty st (subst s pt)) (List.tl sg.sparams) in
              let ps = String.concat "" (List.map (fun p -> ", " ^ p) ps) in
              let ret = cty st (subst s sg.sret) in
              if sig_can_fail_sg sg then Printf.sprintf "uint8_t (*%s)(%s*, StnError*, StnAnyBox*%s);" (vt_member m) ret ps
              else Printf.sprintf "%s (*%s)(StnAnyBox*%s);" ret (vt_member m) ps)
            info.trmethods_
        in
        (* the table body goes with the prototypes, after every aggregate it mentions *)
        pr st.protos "struct StnVt_%s { %s };\n" m (if members = [] then "uint8_t _empty;" else String.concat " " members);
        emit_helpers st t
    | TNamed _ when is_struct st t ->
        let fs = struct_fields st t in
        let fields = List.map (fun (n, t) -> Printf.sprintf "%s %s;" (cty st t) (fname n)) fs in
        let fields = if fields = [] then [ "uint8_t _empty;" ] else fields in
        pr st.typedefs "typedef struct { %s } stn_%s;\n" (String.concat " " fields) m;
        emit_helpers st t
    | TNamed _ when is_data st t -> (
        match layout st t with
        | LInline ->
            let vs = variants st t in
            let members =
              List.filter_map
                (fun ((v : variant_info), fs) ->
                  if fs = [] then None
                  else Some (Printf.sprintf "struct { %s } %s;" (String.concat " " (List.mapi (fun i (_, t) -> Printf.sprintf "%s f%d;" (cty st t) i) fs)) (c_ident v.vname_)))
                vs
            in
            if members = [] then pr st.typedefs "typedef struct { uint8_t tag; } stn_%s;\n" m
            else pr st.typedefs "typedef struct { uint8_t tag; union { %s } u; } stn_%s;\n" (String.concat " " members) m;
            emit_helpers st t
        | LBoxed ->
            pr st.fwd "typedef struct box_%s* stn_%s;\n" m m;
            Queue.add (t, m) st.pending_boxed)
    | _ -> ()
  end

and flush_boxed st =
  while not (Queue.is_empty st.pending_boxed) do
    let t, m = Queue.pop st.pending_boxed in
    let vs = variants st t in
    let members =
      List.filter_map
        (fun ((v : variant_info), fs) ->
          if fs = [] then None
          else Some (Printf.sprintf "struct { %s } %s;" (String.concat " " (List.mapi (fun i (_, t) -> Printf.sprintf "%s f%d;" (cty st t) i) fs)) (c_ident v.vname_)))
        vs
    in
    pr st.boxed_bodies "struct box_%s { stn_header h; union { %s } u; };\n" m
      (if members = [] then "uint8_t _empty;" else String.concat " " members);
    emit_helpers st t
  done

(* dup_M / drop_M and the element operations used by arrays *)
and emit_helpers st t =
  let m = mangle t in
  let c = "stn_" ^ m in
  if needs_rc st t then begin
    pr st.protos "static inline %s dup_%s(%s x);\nstatic inline void drop_%s(%s x);\n" c m c m c;
    match repr t with
    | TAny _ ->
        pr st.helpers "static inline %s dup_%s(%s x) { stn_dup(x.box); return x; }\n" c m c;
        pr st.helpers "static inline void drop_%s(%s x) { stn_any_drop(x.box); }\n" m c
    | TTuple ts ->
        pr st.helpers "static inline %s dup_%s(%s x) { %s return x; }\n" c m c
          (String.concat " " (List.mapi (fun i t -> if needs_rc st t then dup_stmt st t (Printf.sprintf "x.f%d" i) else "") ts));
        pr st.helpers "static inline void drop_%s(%s x) { %s }\n" m c
          (String.concat " " (List.mapi (fun i t -> if needs_rc st t then drop_stmt st t (Printf.sprintf "x.f%d" i) else "") ts))
    | TNamed _ when is_struct st t ->
        let fs = struct_fields st t in
        pr st.helpers "static inline %s dup_%s(%s x) { %s return x; }\n" c m c
          (String.concat " " (List.map (fun (n, t) -> if needs_rc st t then dup_stmt st t ("x." ^ fname n) else "") fs));
        pr st.helpers "static inline void drop_%s(%s x) { %s }\n" m c
          (String.concat " " (List.map (fun (n, t) -> if needs_rc st t then drop_stmt st t ("x." ^ fname n) else "") fs))
    | TNamed _ when layout st t = LInline ->
        let arms f =
          String.concat " "
            (List.map
               (fun ((v : variant_info), fs) ->
                 let body = String.concat " " (List.mapi (fun i (_, t) -> if needs_rc st t then f t (Printf.sprintf "x.u.%s.f%d" (c_ident v.vname_) i) else "") fs) in
                 if body = "" then "" else Printf.sprintf "case %d: %s break;" v.vindex body)
               (variants st t))
        in
        pr st.helpers "static inline %s dup_%s(%s x) { switch (x.tag) { %s default: break; } return x; }\n" c m c (arms (dup_stmt st));
        pr st.helpers "static inline void drop_%s(%s x) { switch (x.tag) { %s default: break; } }\n" m c (arms (drop_stmt st))
    | TNamed _ ->
        (* boxed: one release function per type (section 11.2) *)
        pr st.protos "static void release_%s(void* p);\n" m;
        let arms =
          String.concat " "
            (List.map
               (fun ((v : variant_info), fs) ->
                 let body = String.concat " " (List.mapi (fun i (_, t) -> if needs_rc st t then drop_stmt st t (Printf.sprintf "x->u.%s.f%d" (c_ident v.vname_) i) else "") fs) in
                 if body = "" then "" else Printf.sprintf "case %d: %s break;" v.vindex body)
               (variants st t))
        in
        pr st.helpers "static void release_%s(void* p) { %s x = (%s)p; switch (x->h.tag) { %s default: break; } stn_free(p); }\n" m c c arms;
        pr st.helpers "static inline %s dup_%s(%s x) { stn_dup(x); return x; }\n" c m c;
        pr st.helpers "static inline void drop_%s(%s x) { stn_drop(x, release_%s); }\n" m c m
    | _ -> ()
  end

and dup_stmt st t e =
  match repr t with
  | TStr | TArray _ | TFn _ -> Printf.sprintf "stn_dup(%s);" e
  | TErr _ -> Printf.sprintf "stn_error_dup(%s);" e
  | _ -> ensure_type st t; Printf.sprintf "dup_%s(%s);" (mangle t) e

and drop_stmt st t e =
  match repr t with
  | TNamed ("__cell", [ ct_ ]) -> Printf.sprintf "stn_drop(%s, release_cell_%s);" e (mangle ct_)
  | TNamed ("__unbusy", _) -> Printf.sprintf "%s->busy = 0;" e
  | TStr -> Printf.sprintf "STN_STR_DROP(%s);" e
  | TArray _ -> Printf.sprintf "stn_drop(%s, stn_array_release);" e
  | TFn _ -> Printf.sprintf "stn_closure_drop(%s);" e
  | TErr _ -> Printf.sprintf "stn_error_drop(%s);" e
  | _ -> ensure_type st t; Printf.sprintf "drop_%s(%s);" (mangle t) e

let dup_expr st t e =
  if not (needs_rc st t) then e
  else
    match repr t with
    | TStr | TArray _ | TFn _ -> Printf.sprintf "(stn_dup(%s), %s)" e e
    | TErr _ -> Printf.sprintf "stn_error_dup(%s)" e
    | _ -> Printf.sprintf "dup_%s(%s)" (mangle t) e

let elem_ops st t =
  let m = mangle t in
  let name = "ops_" ^ m in
  if not (Hashtbl.mem st.defined name) then begin
    Hashtbl.replace st.defined name ();
    let c = cty st t in
    if needs_rc st t then begin
      pr st.protos "static void eldup_%s(void* p);\nstatic void eldrop_%s(void* p);\n" m m;
      pr st.helpers "static void eldup_%s(void* p) { %s }\n" m (dup_stmt st t (Printf.sprintf "(*(%s*)p)" c));
      pr st.helpers "static void eldrop_%s(void* p) { %s }\n" m (drop_stmt st t (Printf.sprintf "(*(%s*)p)" c));
      pr st.protos "static const StnElemOps %s;\n" name;
      pr st.helpers "static const StnElemOps %s = { sizeof(%s), eldup_%s, eldrop_%s };\n" name c m m
    end else begin
      pr st.protos "static const StnElemOps %s;\n" name;
      pr st.helpers "static const StnElemOps %s = { sizeof(%s), NULL, NULL };\n" name c
    end
  end;
  "&" ^ name

(* tag of a data value *)
let tag_of st t e =
  match layout st t with
  | LInline -> Printf.sprintf "(%s).tag" e
  | LBoxed -> Printf.sprintf "(((uintptr_t)(%s) & 1) ? (int)((uintptr_t)(%s) >> 1) : (int)(%s)->h.tag)" e e e

let variant_field st t (v : variant_info) i e =
  match layout st t with
  | LInline -> Printf.sprintf "(%s).u.%s.f%d" e (c_ident v.vname_) i
  | LBoxed -> Printf.sprintf "(%s)->u.%s.f%d" e (c_ident v.vname_) i

(* ---------- string literals and errors ---------- *)

let str_lit st s =
  match Hashtbl.find_opt st.strlits s with
  | Some n -> n
  | None ->
      let n = fresh st "strlit" in
      Hashtbl.replace st.strlits s n;
      pr st.helpers "static struct { stn_header h; int64_t len; char data[%d]; } %s_obj = { { 1, 0, STN_NOCOUNT, 0 }, %d, %s };\n"
        (String.length s + 1) n (String.length s) (c_string s);
      pr st.helpers "#define %s ((StnStr)&%s_obj)\n" n n;
      n

let err_id st t =
  let key = mangle t in
  match Hashtbl.find_opt st.errtypes key with
  | Some (id, _) -> id
  | None ->
      let id = Hashtbl.length st.errtypes + 1 in
      Hashtbl.replace st.errtypes key (id, t);
      let c = cty st t in
      pr st.protos "typedef struct { StnErrBox base; %s value; } errbox_%s;\nstatic StnError errmake_%s(%s v);\n" c key key c;
      pr st.helpers "static void errbox_release_%s(void* p) { %s stn_free(p); }\n" key
        (if needs_rc st t then drop_stmt st t (Printf.sprintf "((errbox_%s*)p)->value" key) else "");
      pr st.helpers "static StnError errmake_%s(%s v) { errbox_%s* b = (errbox_%s*)stn_alloc(sizeof *b); b->base.release = errbox_release_%s; b->value = v; return (StnError){ %d, &b->base }; }\n"
        key c key key key id;
      id

let err_val st t e = Printf.sprintf "(((errbox_%s*)(%s).box)->value)" (mangle t) e

(* ---------- function contexts ---------- *)

type vinfo = VDirect of string | VPtr of string | VCell of string * ty | VCap of string | VCapCell of string * ty

type fkind = FScope | FStmt | FLoop | FTry of string * string | FFun

type frame = { fk : fkind; mutable owned : (string * ty) list }

type fc = {
  st : st;
  b : Buffer.t;
  mutable ind : int;
  sub : (string * ty) list;
  mutable frames : frame list;
  can_fail : bool;
  ret : ty;
  vars : (int, vinfo) Hashtbl.t;
  self_struct : string option;
  cached : (int, string * string) Hashtbl.t;  (* arrays hoisted for a loop: data and length names *)
  lend : bool option;                          (* compiling a lend function (lend mut when Some true) *)
}

type r = { c : string; owned : bool }

let line fc fmt = Printf.ksprintf (fun s -> Buffer.add_string fc.b (String.make (2 * fc.ind) ' '); Buffer.add_string fc.b s; Buffer.add_char fc.b '\n') fmt

let ts fc t = subst fc.sub t
let ct fc t = cty fc.st (ts fc t)
let rc fc t = needs_rc fc.st (ts fc t)

let loc_args (l : Syntax.loc) = Printf.sprintf "%s, %d, %d" (c_string l.file) l.line l.col

let push fc fk = fc.frames <- { fk; owned = [] } :: fc.frames

let emit_drops fc (f : frame) = List.iter (fun (n, t) -> line fc "%s" (drop_stmt fc.st t n)) f.owned

let pop fc =
  match fc.frames with
  | f :: rest -> emit_drops fc f; fc.frames <- rest
  | [] -> assert false

(* register an owned value to release when the innermost frame ends *)
let own_in fc name t = match fc.frames with f :: _ -> f.owned <- (name, ts fc t) :: f.owned | [] -> assert false

let tmp fc t init =
  let n = fresh fc.st "_t" in
  line fc "%s %s = %s;" (ct fc t) n init;
  n

let own fc (x : r) t = if x.owned || not (rc fc t) then x.c else dup_expr fc.st (ts fc t) x.c

let borrow fc (x : r) t =
  if x.owned && rc fc t then begin
    let n = tmp fc t x.c in
    own_in fc n t;
    n
  end else x.c

(* drop everything up to (not including) the first frame satisfying [stop] *)
let drop_until fc stop =
  let rec go = function
    | [] -> ()
    | f :: rest -> if stop f then () else (emit_drops fc f; go rest)
  in
  go fc.frames

(* propagate a failure held in [e]: to the nearest try, or out of the function *)
let propagate fc (e : string) =
  let rec find = function
    | [] -> None
    | { fk = FTry (lbl, ev); _ } :: _ -> Some (lbl, ev)
    | _ :: rest -> find rest
  in
  match find fc.frames with
  | Some (lbl, ev) ->
      drop_until fc (fun f -> match f.fk with FTry _ -> true | _ -> false);
      line fc "%s = %s; goto %s;" ev e lbl
  | None ->
      drop_until fc (fun _ -> false);
      if fc.can_fail then line fc "*_err = %s; return 1;" e
      else line fc "stn_trap(\"unhandled failure\", __FILE__, __LINE__, 0, \"a failure reached a function that cannot fail\");"

let request_instance : (st -> string -> ty list -> string) ref = ref (fun _ _ _ -> assert false)

let apply_convs fc convs e =
  List.iter
    (fun cv ->
      let from = ts fc cv.cfrom and target = ts fc cv.cto in
      let fid = err_id fc.st from in
      ignore (err_id fc.st target);
      let fn = !request_instance fc.st cv.cfn [] in
      let v = fresh fc.st "_cv" in
      line fc "if (%s.type_id == %d) { %s %s = %s(%s); stn_error_drop(%s); %s = errmake_%s(%s); }" e fid (cty fc.st target) v fn
        (dup_expr fc.st from (err_val fc.st from e)) e e (mangle target) v)
    convs

(* ---------- signatures ---------- *)

let is_poly_param t = match repr t with TFn f -> f.feff.poly | _ -> false

let sig_can_fail (sg : fsig) =
  sg.seff.errs <> [] || List.exists (fun (_, _, t, _) -> is_poly_param t) sg.sparams

let fn_can_fail_ty (f : fnty) = f.feff.errs <> [] || f.feff.poly

let inst_name uname targs =
  "fn_" ^ c_ident uname ^ (if targs = [] then "" else "__" ^ String.concat "__" (List.map mangle_eff targs))

let param_decl st m t name =
  match m with
  (* exclusivity (section 4.3) means nothing else reaches a mut parameter's storage *)
  | MMut -> Printf.sprintf "%s* restrict %s" (cty st t) name
  | _ -> Printf.sprintf "%s %s" (cty st t) name

let var_name (v : var) = Printf.sprintf "v%d_%s" v.vid (c_ident v.vname)

(* cells (section 13.3) *)
let cell_type st t =
  let m = mangle t in
  let n = "cell_" ^ m in
  if not (Hashtbl.mem st.defined n) then begin
    Hashtbl.replace st.defined n ();
    pr st.typedefs "typedef struct { stn_header h; uint8_t busy; %s value; } %s;\n" (cty st t) n;
    pr st.protos "static void release_%s(void* p);\n" n;
    pr st.helpers "static void release_%s(void* p) { %s stn_free(p); }\n" n
      (if needs_rc st t then drop_stmt st t (Printf.sprintf "((%s*)p)->value" n) else "")
  end;
  n

let var_read fc (v : var) : string =
  match Hashtbl.find_opt fc.vars v.vid with
  | Some (VDirect n) -> n
  | Some (VPtr n) -> "(*" ^ n ^ ")"
  | Some (VCell (n, _)) -> n ^ "->value"
  | Some (VCap n) -> n
  | Some (VCapCell (n, _)) -> n ^ "->value"
  | None -> failwith ("cgen: unbound variable " ^ v.vname)

let is_cell fc (v : var) = match Hashtbl.find_opt fc.vars v.vid with Some (VCell _ | VCapCell _) -> true | _ -> false

let cell_ptr fc (v : var) = match Hashtbl.find_opt fc.vars v.vid with Some (VCell (n, _)) | Some (VCapCell (n, _)) -> n | _ -> assert false

(* ---------- expressions ---------- *)

let int_suffix k s =
  match k with
  | U64 -> Printf.sprintf "UINT64_C(%s)" s
  | U32 -> Printf.sprintf "UINT32_C(%s)" s
  | IInt | I64 ->
      if s = "9223372036854775808" then "INT64_MIN" else Printf.sprintf "INT64_C(%s)" s
  | _ -> s

let float_lit f =
  let s = Printf.sprintf "%.17g" f in
  if String.contains s '.' || String.contains s 'e' || String.contains s 'n' || String.contains s 'i' then s else s ^ ".0"

let kname = function
  | IInt | I64 -> "i64" | I32 -> "i32" | I16 -> "i16" | I8 -> "i8"
  | U64 -> "u64" | U32 -> "u32" | U16 -> "u16" | U8 -> "u8"

let unsigned_of = function
  | IInt | I64 | U64 -> "uint64_t" | I32 | U32 -> "uint32_t" | I16 | U16 -> "uint16_t" | I8 | U8 -> "uint8_t"

(* Some m when [e] calls a lend function (section 4.6) *)
let lend_sig fc (e : texpr) : bool option =
  match e.e with
  | XCall (CFn (u, _), _, _) -> (Hashtbl.find fc.st.prog.fns u).fsig.slend
  | XCall (CTrait (tr, ta, m, self), _, _) -> (
      match Typecheck.impl_method_in (Typecheck.rtab_of_prog fc.st.prog) tr (List.map (ts fc) ta) m (ts fc self) with
      | Some (f, _) -> (Hashtbl.find fc.st.prog.fns f).fsig.slend
      | None -> None)
  | _ -> None

(* a C operand that cannot trap or have effects: a name, a dereferenced name, a number *)
let simple_operand (c : string) =
  let ident_char ch = (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch = '_' || ch = '.' in
  let c = if String.length c > 3 && String.sub c 0 2 = "(*" && c.[String.length c - 1] = ')' then String.sub c 2 (String.length c - 3) else c in
  let c =
    (* INT64_C(5), UINT64_C(5) *)
    match String.index_opt c '(' with
    | Some i when (String.sub c 0 i = "INT64_C" || String.sub c 0 i = "UINT64_C" || String.sub c 0 i = "UINT32_C") && c.[String.length c - 1] = ')' ->
        String.sub c (i + 1) (String.length c - i - 2)
    | _ -> c
  in
  c <> "" && String.for_all (fun ch -> ident_char ch || ch = '-') c

(* The value of a block that ends in return, break, continue, fail or lend: the checker
   gives it the block's type, but control never reaches it. *)
let unreachable_value fc (e : texpr) =
  repr (ts fc e.ty) = TNever
  || (match (e.e, repr (ts fc e.ty)) with XLit LUnit, TUnit -> false | XLit LUnit, _ -> true | _ -> false)

let rec expr fc (e : texpr) : r =
  let st = fc.st in
  let t = ts fc e.ty in
  match e.e with
  | XLit l -> lit fc t l
  | XNone -> { c = "0"; owned = false }
  | XFStr ps ->
      let parts = List.map (fun p -> borrow fc (expr fc p) TStr) ps in
      (match parts with
       | [ p ] -> { c = p; owned = false }
       | _ -> { c = tmp fc TStr (Printf.sprintf "stn_str_concat_n(%d, (StnStr[]){ %s })" (List.length parts) (String.concat ", " parts)); owned = true })
  | XVar v ->
      if is_cell fc v then begin
        let p = cell_ptr fc v in
        line fc "if (%s->busy) stn_trap(\"shared cell busy\", %s, \"a shared cell was accessed while it was lent out\");" p (loc_args e.l);
        if rc fc v.vty then { c = tmp fc v.vty (dup_expr st (ts fc v.vty) (var_read fc v)); owned = true }
        else { c = var_read fc v; owned = false }
      end else { c = var_read fc v; owned = false }
  | XFnRef (n, tys) -> { c = fn_closure fc n (List.map (ts fc) tys); owned = false }
  | XCall (cl, args, convs) -> call fc e cl args convs
  | XField (b, _, f) ->
      let bv = borrow fc (expr fc b) b.ty in
      { c = Printf.sprintf "(%s).%s" bv (fname f); owned = false }
  | XTupleGet (b, i) ->
      let bv = borrow fc (expr fc b) b.ty in
      { c = Printf.sprintf "(%s).f%d" bv i; owned = false }
  | XIndex ({ e = XVar v; _ }, i) when Hashtbl.mem fc.cached v.vid ->
      let d, n = Hashtbl.find fc.cached v.vid in
      let iv = tmp fc (TInt IInt) (expr fc i).c in
      { c = Printf.sprintf "%s[stn_index(%s, %s, %s)]" d iv n (loc_args e.l); owned = false }
  | XIndex (a, i) ->
      let av = borrow fc (expr fc a) a.ty in
      let iv = (expr fc i).c in
      let iv = tmp fc (TInt IInt) iv in
      { c = Printf.sprintf "((%s*)(%s)->data)[stn_index(%s, stn_len(%s), %s)]" (ct fc t) av iv av (loc_args e.l); owned = false }
  | XSlice (a, lo, hi) ->
      let av = borrow fc (expr fc a) a.ty in
      let lov = tmp fc (TInt IInt) (expr fc lo).c in
      let hiv = tmp fc (TInt IInt) (expr fc hi).c in
      (match repr (ts fc a.ty) with
       | TStr -> { c = tmp fc t (Printf.sprintf "stn_str_slice(%s, %s, %s, %s)" av lov hiv (loc_args e.l)); owned = true }
       | _ -> { c = tmp fc t (Printf.sprintf "stn_array_slice(%s, %s, %s, %s)" av lov hiv (loc_args e.l)); owned = true })
  | XTuple es ->
      let vs = List.map (fun x -> own fc (expr fc x) x.ty) es in
      let vs = List.map2 (fun v x -> tmp fc x.ty v) vs es in
      { c = tmp fc t (Printf.sprintf "(%s){ %s }" (ct fc t) (String.concat ", " vs)); owned = true }
  | XArray es ->
      let elt = match repr t with TArray et -> et | _ -> assert false in
      let a = tmp fc t (Printf.sprintf "stn_array_new(%s, %d)" (elem_ops st elt) (max 1 (List.length es))) in
      List.iter
        (fun x ->
          let v = own fc (expr fc x) x.ty in
          let n = tmp fc elt v in
          line fc "STN_PUSH(&%s, %s, %s);" a (cty st elt) n)
        es;
      { c = a; owned = true }
  | XStruct (_, _, es) ->
      let fs = struct_fields st t in
      let vs = List.map (fun x -> tmp fc x.ty (own fc (expr fc x) x.ty)) es in
      let inits = List.map2 (fun (n, _) v -> Printf.sprintf ".%s = %s" (fname n) v) fs vs in
      let inits = if inits = [] then [ "._empty = 0" ] else inits in
      { c = tmp fc t (Printf.sprintf "(%s){ %s }" (ct fc t) (String.concat ", " inits)); owned = true }
  | XVariant (_, _, i, es) -> construct fc t i (List.map (fun x -> tmp fc x.ty (own fc (expr fc x) x.ty)) es)
  | XIf (c, a, b) -> (
      let cv = cond fc c in
      match repr t with
      | TUnit | TNever ->
          line fc "if (%s) {" cv;
          fc.ind <- fc.ind + 1;
          discard fc a;
          fc.ind <- fc.ind - 1;
          line fc "} else {";
          fc.ind <- fc.ind + 1;
          discard fc b;
          fc.ind <- fc.ind - 1;
          line fc "}";
          { c = "0"; owned = false }
      | _ ->
          let res = fresh st "_r" in
          line fc "%s %s;" (ct fc t) res;
          line fc "if (%s) {" cv;
          fc.ind <- fc.ind + 1;
          assign_into fc res a t;
          fc.ind <- fc.ind - 1;
          line fc "} else {";
          fc.ind <- fc.ind + 1;
          assign_into fc res b t;
          fc.ind <- fc.ind - 1;
          line fc "}";
          { c = res; owned = true })
  | XBlock ([], v) -> expr fc v
  | XBlock (ss, v) -> (
      match repr t with
      | TUnit | TNever ->
          line fc "{";
          fc.ind <- fc.ind + 1;
          push fc FScope;
          List.iter (stmt fc) ss;
          discard_value fc v;
          pop fc;
          fc.ind <- fc.ind - 1;
          line fc "}";
          { c = "0"; owned = false }
      | _ ->
          let res = fresh st "_r" in
          line fc "%s %s;" (ct fc t) res;
          line fc "{";
          fc.ind <- fc.ind + 1;
          push fc FScope;
          List.iter (stmt fc) ss;
          push fc FStmt;
          let x = expr fc v in
          if not (unreachable_value fc v) then line fc "%s = %s;" res (own fc x v.ty);
          pop fc;
          pop fc;
          fc.ind <- fc.ind - 1;
          line fc "}";
          { c = res; owned = true })
  | XMatch (s, arms) -> match_ fc t s arms
  | XLambda lam -> { c = closure fc lam; owned = true }
  | XBin (And, a, b) | XBin (Or, a, b) ->
      let is_and = match e.e with XBin (And, _, _) -> true | _ -> false in
      let av = cond fc a in
      (* When the right side needs no statements of its own, C's && and || keep the
         short circuit and let the C compiler see the loop condition as one test. *)
      let mark = Buffer.length fc.b and saved = fc.frames in
      push fc FStmt;
      let bx = expr fc b in
      let simple = Buffer.length fc.b = mark && (List.hd fc.frames).owned = [] && not bx.owned in
      if simple then begin
        fc.frames <- saved;
        { c = Printf.sprintf "(%s %s %s)" av (if is_and then "&&" else "||") bx.c; owned = false }
      end else begin
        (* The right side is already generated, with its frame still open. Move its
           statements inside the conditional instead of generating it a second time:
           regenerating would make right-nested and/or cost exponential work. *)
        let body = Buffer.sub fc.b mark (Buffer.length fc.b - mark) in
        Buffer.truncate fc.b mark;
        let res = tmp fc TBool av in
        line fc "if (%s%s) {" (if is_and then "" else "!") res;
        Buffer.add_string fc.b body;
        fc.ind <- fc.ind + 1;
        let bv = tmp fc TBool bx.c in
        pop fc;
        line fc "%s = %s;" res bv;
        fc.ind <- fc.ind - 1;
        line fc "}";
        { c = res; owned = false }
      end
  | XBin (op, a, b) -> binop fc e op a b
  | XNeg a -> (
      let av = (expr fc a).c in
      match repr t with
      | TInt k -> { c = Printf.sprintf "stn_sub_%s(0, %s, %s)" (kname k) av (loc_args e.l); owned = false }
      | _ -> { c = Printf.sprintf "(-(%s))" av; owned = false })
  | XNot a -> { c = Printf.sprintf "(!(%s))" (expr fc a).c; owned = false }
  | XTry a -> try_ fc t a
  | XConv a -> conv fc e a t
  | XPack a ->
      (* box the value once; the table says which methods to run (section 3.4) *)
      let at = ts fc a.ty in
      (match repr at with
       | TAny _ ->
           (* a generic function instantiated with a trait value: it is one already *)
           expr fc a
       | _ ->
      let vt = any_vtable fc.st e.l t at in
      let v = own fc (expr fc a) a.ty in
      let b = fresh st "_b" in
      line fc "StnAnyBox* %s = (StnAnyBox*)stn_alloc(sizeof(StnAnyBox) + sizeof(%s));" b (cty st at);
      line fc "%s->release = anyrel_%s; *(%s*)%s->data = %s;" b (mangle at) (cty st at) b v;
      { c = tmp fc t (Printf.sprintf "(%s){ %s, &%s }" (ct fc t) b vt); owned = true })
  | XFail a ->
      let at = ts fc a.ty in
      let v = own fc (expr fc a) a.ty in
      let ev = fresh st "_e" in
      (match repr at with
       | TErr _ -> line fc "StnError %s = %s;" ev v
       | _ -> line fc "StnError %s = errmake_%s(%s);" ev (mangle at) v; ignore (err_id st at));
      propagate fc ev;
      { c = "0"; owned = false }
  | XComp (body, comps) ->
      let elt = match repr t with TArray et -> et | _ -> assert false in
      let a = fresh st "_t" in
      (* the result grows by doubling; sizing it up front from the source would evaluate
         the source twice *)
      line fc "StnArray* %s = stn_array_new(%s, 4);" a (elem_ops st elt);
      let rec go = function
        | [] ->
            push fc FStmt;
            let v = own fc (expr fc body) body.ty in
            let n = tmp fc elt v in
            line fc "STN_PUSH(&%s, %s, %s);" a (cty st elt) n;
            pop fc
        | cp :: rest ->
            loop_over fc cp.csrc cp.cvar (fun () ->
                match cp.ccond with
                | Some c ->
                    push fc FStmt;
                    let cv = cond fc c in
                    let k = tmp fc TBool cv in
                    pop fc;
                    line fc "if (%s) {" k;
                    fc.ind <- fc.ind + 1;
                    go rest;
                    fc.ind <- fc.ind - 1;
                    line fc "}"
                | None -> go rest)
      in
      go comps;
      { c = a; owned = true }

and lit fc t (l : lit) : r =
  match l with
  | LInt s -> (
      let v = Values.parse_int_lit s in
      match repr t with
      | TInt k -> { c = int_suffix k (Values.int_to_string k v); owned = false }
      | TFloat -> { c = float_lit (Int64.to_float v); owned = false }
      | TF32 -> { c = float_lit (Int64.to_float v) ^ "f"; owned = false }
      | _ -> { c = Int64.to_string v; owned = false })
  | LFloat f -> { c = (if repr t = TF32 then "((float)" ^ float_lit f ^ ")" else float_lit f); owned = false }
  | LStr s -> { c = str_lit fc.st s; owned = false }
  | LChar c -> { c = string_of_int c; owned = false }
  | LBool b -> { c = (if b then "1" else "0"); owned = false }
  | LUnit -> { c = "0"; owned = false }
  | LDur (n, u) -> { c = Printf.sprintf "INT64_C(%Ld)" (Values.dur_value n u); owned = false }

(* evaluate a Bool expression, releasing its temporaries, into a plain C value *)
and cond fc (e : texpr) : string =
  push fc FStmt;
  let v = (expr fc e).c in
  let n = tmp fc TBool v in
  pop fc;
  n

and discard fc (e : texpr) =
  push fc FStmt;
  discard_value fc e;
  pop fc

and discard_value fc (e : texpr) =
  let x = expr fc e in
  if x.owned && rc fc e.ty then line fc "%s" (drop_stmt fc.st (ts fc e.ty) x.c)
  else if x.c <> "0" && not (String.length x.c > 0 && x.c.[0] = '_') then line fc "(void)(%s);" x.c

and assign_into fc res (e : texpr) t =
  push fc FStmt;
  let x = expr fc e in
  if not (unreachable_value fc e) then line fc "%s = %s;" res (own fc x t);
  pop fc

and construct fc t i (vals : string list) : r =
  let st = fc.st in
  let vs = variants st t in
  let v, _ = List.nth vs i in
  match layout st t with
  | LInline ->
      let inits = List.mapi (fun j x -> Printf.sprintf ".u.%s.f%d = %s" (c_ident v.vname_) j x) vals in
      { c = tmp fc t (Printf.sprintf "(%s){ .tag = %d%s }" (ct fc t) i (String.concat "" (List.map (fun s -> ", " ^ s) inits))); owned = true }
  | LBoxed ->
      if vals = [] then { c = Printf.sprintf "((%s)(uintptr_t)((%d << 1) | 1))" (ct fc t) i; owned = false }
      else begin
        let n = fresh st "_b" in
        line fc "%s %s = (%s)stn_alloc(sizeof(struct box_%s));" (ct fc t) n (ct fc t) (mangle t);
        line fc "%s->h.tag = %d;" n i;
        List.iteri (fun j x -> line fc "%s->u.%s.f%d = %s;" n (c_ident v.vname_) j x) vals;
        { c = n; owned = true }
      end

(* ---------- calls ---------- *)

and args_c fc (params : (mode * ty) list) (targs : targ list) : string list =
  List.map2
    (fun (m, pt) ta ->
      match m with
      | MMut -> let lv = place_lvalue_of_expr fc ta.a in hold_busy fc ta.a; "&" ^ lv
      | MTake -> tmp fc ta.a.ty (own fc (expr fc ta.a) ta.a.ty)
      | MBorrow ->
          let x = expr fc ta.a in
          let v = borrow fc x ta.a.ty in
          v)
    params targs

and call fc (e : texpr) (cl : callee) (targs : targ list) convs : r =
  let st = fc.st in
  let t = ts fc e.ty in
  match cl with
  | CFn (uname, tys) ->
      let tys = List.map (ts fc) tys in
      let tf = Hashtbl.find st.prog.fns uname in
      call_instance fc e uname tys tf.fsig targs convs
  | CBuiltin (name, tys) -> builtin fc e name (List.map (ts fc) tys) targs convs
  | CTrait (tr, ta, m, self) when (match repr (ts fc self) with TAny _ -> true | _ -> false) ->
      any_call fc e tr (List.map (ts fc) ta) m (ts fc self) targs convs
  | CTrait (tr, ta, m, self) -> (
      let self = ts fc self and ta = List.map (ts fc) ta in
      match Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) tr ta m self with
      | Some (f, ftys) ->
          let tf = Hashtbl.find st.prog.fns f in
          call_instance fc e f ftys tf.fsig targs convs
      | None -> prim_trait fc e tr m self targs)
  | CClosure f ->
      let fv = borrow fc (expr fc f) f.ty in
      let fty = match repr (ts fc f.ty) with TFn ft -> ft | _ -> assert false in
      let ps = fty.fps in
      let avs = args_c fc ps targs in
      let res = fresh st "_r" and ev = fresh st "_e" in
      line fc "%s %s; StnError %s;" (ct fc t) res ev;
      let sigc = Printf.sprintf "uint8_t (*)(StnClosure*, %s*, StnError*%s)" (ct fc t)
          (String.concat "" (List.map (fun (m, pt) -> ", " ^ (match m with MMut -> ct fc pt ^ "*" | _ -> ct fc pt)) ps)) in
      line fc "if (__builtin_expect(((%s)%s->code)(%s, &%s, &%s%s), 0)) {" sigc fv fv res ev
        (String.concat "" (List.map (fun a -> ", " ^ a) avs));
      fc.ind <- fc.ind + 1;
      apply_convs fc convs ev;
      propagate fc ev;
      fc.ind <- fc.ind - 1;
      line fc "}";
      { c = res; owned = true }

(* The method table of [any] for the concrete type [at], and the release function of its
   box. One wrapper per method takes the box and forwards the payload to the impl's
   function; an impl that cannot fail is adapted to a trait method that can (section 3.4). *)
and any_vtable st (l : Syntax.loc) (any : ty) (at : ty) : string =
  let tr, ta = match repr any with TAny (tr, ta) -> (tr, ta) | _ -> assert false in
  let info = Hashtbl.find st.prog.traits tr in
  let s = List.combine info.trparams ta in
  let am = mangle any and cm = mangle_eff at in
  let cc = cty st at in
  (* the box is released by the representation of its value alone *)
  let crel = mangle at in
  if not (Hashtbl.mem st.defined ("anyrel_" ^ crel)) then begin
    Hashtbl.replace st.defined ("anyrel_" ^ crel) ();
    pr st.protos "static void anyrel_%s(void* p);\n" crel;
    pr st.helpers "static void anyrel_%s(void* p) { %s stn_free(p); }\n" crel
      (if needs_rc st at then drop_stmt st at (Printf.sprintf "(*(%s*)((StnAnyBox*)p)->data)" cc) else "")
  end;
  let key = "vt_" ^ am ^ "__" ^ cm in
  if not (Hashtbl.mem st.defined key) then begin
    Hashtbl.replace st.defined key ();
    ensure_type st any;
    let entries =
      List.map
        (fun (m, (sg : fsig)) ->
          let recv = Printf.sprintf "*(%s*)b->data" cc in
          let w = Printf.sprintf "vtw_%s__%s__%s" am cm (c_ident m) in
          match Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) tr ta m at with
          | None when tr = "Show" && m = "show" ->
              (* the built-in Show of a primitive, tuple or derived type: formatted by the
                 runtime's own code, as a direct call would *)
              let fc = { st; b = Buffer.create 64; ind = 0; sub = []; frames = []; can_fail = false; ret = TStr; vars = Hashtbl.create 1;
                         self_struct = None; cached = Hashtbl.create 4; lend = None } in
              pr st.helpers "static StnStr %s(StnAnyBox* b) { return %s; }\n" w (show_call fc at (Printf.sprintf "(%s)" recv));
              (m, w)
          | None -> unsupported l "%s cannot be used as %s: its implementation of %s is built in and has no method table" (show_ty at) (show_ty any) tr
          | Some (f, ftys) ->
          let impl_sg = (Hashtbl.find st.prog.fns f).fsig in
          (* the type checker keeps an impl from failing where its trait method cannot; the
             table calls the impl as the trait describes, so the two must agree *)
          if sig_can_fail_sg impl_sg && not (sig_can_fail_sg sg) then
            unsupported l "%s: the impl of %s.%s can fail, but the trait method cannot" (show_ty at) tr m;
          let iname = !request_instance st f ftys in
          let ps = List.mapi (fun i (md, _, pt, _) -> (md, subst s pt, Printf.sprintf "p%d" i)) (List.tl sg.sparams) in
          let ret = cty st (subst s sg.sret) in
          let plist = String.concat "" (List.map (fun (md, pt, n) -> ", " ^ param_decl st md pt n) ps) in
          let args = String.concat "" (List.map (fun (_, _, n) -> ", " ^ n) ps) in
          (if sig_can_fail_sg sg then begin
             if sig_can_fail_sg impl_sg then
               pr st.helpers "static uint8_t %s(%s* _out, StnError* _err, StnAnyBox* b%s) { return %s(_out, _err, %s%s); }\n" w ret plist iname recv args
             else
               pr st.helpers "static uint8_t %s(%s* _out, StnError* _err, StnAnyBox* b%s) { *_out = %s(%s%s); return 0; }\n" w ret plist iname recv args
           end else
             pr st.helpers "static %s %s(StnAnyBox* b%s) { return %s(%s%s); }\n" ret w plist iname recv args);
          (m, w))
        info.trmethods_
    in
    pr st.helpers "static const StnVt_%s %s = { %s };\n" am key
      (if entries = [] then "0" else String.concat ", " (List.map (fun (m, w) -> Printf.sprintf ".%s = %s" (vt_member m) w) entries))
  end;
  key

(* a call of a trait method on a trait value: through the method table of its box *)
and any_call fc (e : texpr) tr ta m (self : ty) (targs : targ list) convs : r =
  let st = fc.st in
  let t = ts fc e.ty in
  ensure_type st self;
  let info = Hashtbl.find st.prog.traits tr in
  let sg = List.assoc m info.trmethods_ in
  let s = List.combine info.trparams ta in
  let ps = List.map (fun (md, _, pt, _) -> (md, subst s pt)) (List.tl sg.sparams) in
  let recv = List.hd targs in
  let rv = tmp fc self (borrow fc (expr fc recv.a) recv.a.ty) in
  let avs = args_c fc ps (List.tl targs) in
  let rest = String.concat "" (List.map (fun a -> ", " ^ a) avs) in
  let fp = Printf.sprintf "%s.vt->%s" rv (vt_member m) in
  if sig_can_fail_sg sg then begin
    let res = fresh st "_r" and ev = fresh st "_e" in
    line fc "%s %s; StnError %s;" (ct fc t) res ev;
    line fc "if (__builtin_expect(%s(&%s, &%s, %s.box%s), 0)) {" fp res ev rv rest;
    fc.ind <- fc.ind + 1;
    apply_convs fc convs ev;
    propagate fc ev;
    fc.ind <- fc.ind - 1;
    line fc "}";
    { c = res; owned = true }
  end else
    { c = tmp fc t (Printf.sprintf "%s(%s.box%s)" fp rv rest); owned = true }

and call_instance fc (e : texpr) uname tys (sg : fsig) targs convs : r =
  let st = fc.st in
  let t = ts fc e.ty in
  let name = !request_instance st uname tys in
  let s = List.combine (List.map fst sg.stparams) tys in
  let ps = List.map (fun (m, _, pt, _) -> (m, subst s pt)) sg.sparams in
  if sg.slend <> None then begin
    (* every parameter it can lend from is passed by address, so the place outlives
       the call; the pointer is good for the rest of the caller's statement *)
    let avs =
      List.map2
        (fun (m, _) ta ->
          match m with
          | MMut -> let lv = place_lvalue_of_expr fc ta.a in hold_busy fc ta.a; "&" ^ lv
          | MTake -> tmp fc ta.a.ty (own fc (expr fc ta.a) ta.a.ty)
          | MBorrow -> (
              match to_place fc ta.a with
              | Some p -> "&" ^ place_lvalue ~write:false fc p
              | None -> "&" ^ tmp fc ta.a.ty (borrow fc (expr fc ta.a) ta.a.ty)))
        ps targs
    in
    let p = fresh st "_lp" in
    line fc "%s* %s = %s(%s);" (ct fc t) p name (String.concat ", " avs);
    { c = "(*" ^ p ^ ")"; owned = false }
  end else
  let avs = args_c fc ps targs in
  if sig_can_fail sg then begin
    let res = fresh st "_r" and ev = fresh st "_e" in
    line fc "%s %s; StnError %s;" (ct fc t) res ev;
    line fc "if (__builtin_expect(%s(&%s, &%s%s), 0)) {" name res ev (String.concat "" (List.map (fun a -> ", " ^ a) avs));
    fc.ind <- fc.ind + 1;
    apply_convs fc convs ev;
    propagate fc ev;
    fc.ind <- fc.ind - 1;
    line fc "}";
    { c = res; owned = true }
  end else
    { c = tmp fc t (Printf.sprintf "%s(%s)" name (String.concat ", " avs)); owned = true }

(* a named function used as a value: a constant closure object (section 13.1) *)
and fn_closure fc uname tys : string =
  let st = fc.st in
  let key = "fnclo_" ^ inst_name uname tys in
  if not (Hashtbl.mem st.defined key) then begin
    Hashtbl.replace st.defined key ();
    let tf = Hashtbl.find st.prog.fns uname in
    let sg = tf.fsig in
    let s = List.combine (List.map fst sg.stparams) tys in
    let ps = List.mapi (fun i (m, _, pt, _) -> (m, subst s pt, Printf.sprintf "a%d" i)) sg.sparams in
    let ret = subst s sg.sret in
    let name = !request_instance st uname tys in
    let b = Buffer.create 256 in
    pr b "static uint8_t %s_code(StnClosure* self, %s* out, StnError* err%s) {\n" key (cty st ret)
      (String.concat "" (List.map (fun (m, t, n) -> ", " ^ param_decl st m t n) ps));
    (* a take parameter arrives owned; the callee takes it over *)
    if sig_can_fail sg then pr b "  return %s(out, err%s);\n}\n" name (String.concat "" (List.map (fun (_, _, n) -> ", " ^ n) ps))
    else pr b "  *out = %s(%s);\n  return 0;\n}\n" name (String.concat ", " (List.map (fun (_, _, n) -> n) ps));
    pr st.protos "static uint8_t %s_code(StnClosure* self, %s* out, StnError* err%s);\n" key (cty st ret)
      (String.concat "" (List.map (fun (m, t, n) -> ", " ^ param_decl st m t n) ps));
    Buffer.add_buffer st.funcs b;
    pr st.helpers "static StnClosure %s = { { 1, 0, STN_NOCOUNT, 0 }, (void*)%s_code, NULL };\n" key key
  end;
  "(&" ^ key ^ ")"

and prim_trait fc (e : texpr) tr m self (targs : targ list) : r =
  let st = fc.st in
  let args () = List.map (fun ta -> borrow fc (expr fc ta.a) ta.a.ty) targs in
  match tr with
  | "Show" -> (
      let a = List.hd (args ()) in
      { c = tmp fc TStr (show_call fc self a); owned = true })
  | "Eq" ->
      let a = args () in
      { c = eq_call fc self (List.nth a 0) (List.nth a 1); owned = false }
  | "Ord" ->
      let a = args () in
      { c = cmp_call fc self (List.nth a 0) (List.nth a 1); owned = false }
  | "Add" | "Sub" | "Mul" | "Div" ->
      let op = match tr with "Add" -> Add | "Sub" -> Sub | "Mul" -> Mul | _ -> Div in
      (match targs with
       | [ a; b ] -> binop fc e op a.a b.a
       | _ -> assert false)
  | "Default" -> (
      match repr self with
      | TStr -> { c = str_lit st ""; owned = false }
      | TFloat | TF32 -> { c = "0.0"; owned = false }
      | _ -> { c = "0"; owned = false })
  | "Hash" -> { c = "0"; owned = false }
  | _ -> unsupported e.l "trait %s on %s" tr (show_ty self)

(* show: an owned StnStr for a borrowed value *)
and show_call fc t (a : string) : string =
  let st = fc.st in
  match repr t with
  | TInt U64 -> Printf.sprintf "stn_show_u64(%s)" a
  | TInt (U32 | U16 | U8) -> Printf.sprintf "stn_show_i64((int64_t)%s)" a
  | TInt _ -> Printf.sprintf "stn_show_i64((int64_t)%s)" a
  | TFloat -> Printf.sprintf "stn_show_f64(%s)" a
  | TF32 -> Printf.sprintf "stn_show_f32(%s)" a
  | TBool -> Printf.sprintf "stn_show_bool(%s)" a
  | TChar -> Printf.sprintf "stn_show_char(%s)" a
  | TUnit | TNever -> "stn_show_unit()"
  | TStr -> Printf.sprintf "(stn_dup(%s), %s)" a a
  | TDur -> Printf.sprintf "stn_show_dur(%s)" a
  | TBytes -> Printf.sprintf "stn_show_bytes(%s)" a
  | TErr _ -> Printf.sprintf "stn_show_error(%s)" a
  | TAny ("Show", _) -> Printf.sprintf "%s.vt->%s(%s.box)" a (vt_member "show") a
  | _ -> (
      match Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) "Show" [] "show" t with
      | Some (f, ftys) -> Printf.sprintf "%s(%s)" (!request_instance st f ftys) a
      | None -> (
          match repr t with
          | TTuple ts ->
              let n = "show_" ^ mangle t in
              if not (Hashtbl.mem st.defined n) then begin
                Hashtbl.replace st.defined n ();
                pr st.protos "static StnStr %s(%s x);\n" n (cty st t);
                let parts = List.mapi (fun i et -> Printf.sprintf "%s" (show_call fc et (Printf.sprintf "x.f%d" i))) ts in
                let k = List.length ts in
                let b = Buffer.create 256 in
                pr b "static StnStr %s(%s x) {\n  StnStr p[%d];\n" n (cty st t) (2 * k + 1);
                List.iteri (fun i p -> pr b "  p[%d] = %s;\n" (2 * i + 1) p) parts;
                pr b "  p[0] = %s;\n" (str_lit st "(");
                for i = 1 to k - 1 do pr b "  p[%d] = %s;\n" (2 * i) (str_lit st ", ") done;
                pr b "  p[%d] = %s;\n" (2 * k) (str_lit st ")");
                pr b "  StnStr r = stn_str_concat_n(%d, p);\n" (2 * k + 1);
                List.iteri (fun i _ -> pr b "  STN_STR_DROP(p[%d]);\n" (2 * i + 1)) parts;
                pr b "  return r;\n}\n";
                Buffer.add_buffer st.funcs b
              end;
              Printf.sprintf "%s(%s)" n a
          | _ -> Printf.sprintf "stn_str_new(%s, %d)" (c_string ("<" ^ show_ty t ^ ">")) (String.length (show_ty t) + 2)))

and eq_call fc t a b : string =
  let st = fc.st in
  match repr t with
  | TStr -> Printf.sprintf "stn_str_eq(%s, %s)" a b
  | TInt _ | TFloat | TF32 | TBool | TChar | TDur | TBytes -> Printf.sprintf "((%s) == (%s))" a b
  | TUnit | TNever -> "1"
  | _ -> (
      match Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) "Eq" [] "eq" t with
      | Some (f, ftys) -> Printf.sprintf "%s(%s, %s)" (!request_instance st f ftys) a b
      | None ->
          let n = "eq_" ^ mangle t in
          if not (Hashtbl.mem st.defined n) then begin
            Hashtbl.replace st.defined n ();
            let c = cty st t in
            pr st.protos "static uint8_t %s(%s x, %s y);\n" n c c;
            let body =
              match repr t with
              | TArray et ->
                  Printf.sprintf "if (x->len != y->len) return 0; for (int64_t i = 0; i < x->len; i++) { %s ex = ((%s*)x->data)[i]; %s ey = ((%s*)y->data)[i]; if (!%s) return 0; } return 1;"
                    (cty st et) (cty st et) (cty st et) (cty st et) (eq_call fc et "ex" "ey")
              | TTuple ts -> "return " ^ String.concat " && " ("1" :: List.mapi (fun i et -> eq_call fc et (Printf.sprintf "x.f%d" i) (Printf.sprintf "y.f%d" i)) ts) ^ ";"
              | TNamed _ when is_struct st t ->
                  "return " ^ String.concat " && " ("1" :: List.map (fun (fnm, et) -> eq_call fc et ("x." ^ fname fnm) ("y." ^ fname fnm)) (struct_fields st t)) ^ ";"
              | TNamed _ ->
                  let arms =
                    List.map
                      (fun ((v : variant_info), fs) ->
                        Printf.sprintf "case %d: return %s;" v.vindex
                          (String.concat " && " ("1" :: List.mapi (fun i (_, et) -> eq_call fc et (variant_field st t v i "x") (variant_field st t v i "y")) fs)))
                      (variants st t)
                  in
                  Printf.sprintf "if (%s != %s) return 0; switch (%s) { %s } return 1;" (tag_of st t "x") (tag_of st t "y") (tag_of st t "x") (String.concat " " arms)
              | TErr _ -> "return x.type_id == y.type_id;"
              | _ -> "return 0;"
            in
            pr st.helpers "static uint8_t %s(%s x, %s y) { %s }\n" n c c body
          end;
          Printf.sprintf "%s(%s, %s)" n a b)

and cmp_call fc t a b : string =
  let st = fc.st in
  match repr t with
  | TStr -> Printf.sprintf "((int64_t)stn_str_cmp(%s, %s))" a b
  | TInt _ | TFloat | TF32 | TBool | TChar | TDur | TBytes -> Printf.sprintf "((int64_t)(((%s) > (%s)) - ((%s) < (%s))))" a b a b
  | _ -> (
      match Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) "Ord" [] "cmp" t with
      | Some (f, ftys) -> Printf.sprintf "%s(%s, %s)" (!request_instance st f ftys) a b
      | None -> "0")

and binop fc (e : texpr) op (a : texpr) (b : texpr) : r =
  let st = fc.st in
  let at = ts fc a.ty in
  let ab = borrow fc (expr fc a) a.ty in
  (* Operands are evaluated left to right (section 4.4), but C leaves the order of a
     call's arguments open, and either side may trap. So the left operand stays an
     expression only when it is a variable or a literal and the right one emits no
     statements; otherwise it is saved in a temporary ahead of the right one's code. *)
  let mark = Buffer.length fc.b in
  let bb = borrow fc (expr fc b) b.ty in
  let ab =
    if rc fc a.ty || (Buffer.length fc.b = mark && simple_operand ab) then ab
    else begin
      let right = Buffer.sub fc.b mark (Buffer.length fc.b - mark) in
      Buffer.truncate fc.b mark;
      let n = tmp fc a.ty ab in
      Buffer.add_string fc.b right;
      n
    end
  in
  let la = loc_args e.l in
  let plain o = { c = Printf.sprintf "((%s) %s (%s))" ab o bb; owned = false } in
  match (op, repr at) with
  | (Eq | Ne | Lt | Le | Gt | Ge), TStr ->
      let c = match op with
        | Eq -> Printf.sprintf "stn_str_eq(%s, %s)" ab bb
        | Ne -> Printf.sprintf "(!stn_str_eq(%s, %s))" ab bb
        | Lt -> Printf.sprintf "(stn_str_cmp(%s, %s) < 0)" ab bb
        | Le -> Printf.sprintf "(stn_str_cmp(%s, %s) <= 0)" ab bb
        | Gt -> Printf.sprintf "(stn_str_cmp(%s, %s) > 0)" ab bb
        | _ -> Printf.sprintf "(stn_str_cmp(%s, %s) >= 0)" ab bb in
      { c; owned = false }
  | (Eq | Ne), (TUnit | TNever) -> { c = (if op = Eq then "1" else "0"); owned = false }
  | Eq, _ -> plain "=="
  | Ne, _ -> plain "!="
  | Lt, _ -> plain "<"
  | Le, _ -> plain "<="
  | Gt, _ -> plain ">"
  | Ge, _ -> plain ">="
  | Add, TStr -> { c = tmp fc TStr (Printf.sprintf "stn_str_concat(%s, %s)" ab bb); owned = true }
  | (Add | Sub | Mul | Div | Mod), (TInt k) ->
      let f = match op with Add -> "add" | Sub -> "sub" | Mul -> "mul" | Div -> "div" | _ -> "rem" in
      { c = Printf.sprintf "stn_%s_%s(%s, %s, %s)" f (kname k) ab bb la; owned = false }
  | (Add | Sub), (TDur | TBytes) ->
      { c = Printf.sprintf "stn_%s_i64(%s, %s, %s)" (if op = Add then "add" else "sub") ab bb la; owned = false }
  | (AddW | SubW | MulW), TInt k ->
      let o = match op with AddW -> "+" | SubW -> "-" | _ -> "*" in
      let u = unsigned_of k in
      { c = Printf.sprintf "((%s)(%s)((%s)(%s) %s (%s)(%s)))" (ct fc at) u u ab o u bb; owned = false }
  | Mod, (TFloat | TF32) -> { c = Printf.sprintf "fmod(%s, %s)" ab bb; owned = false }
  | Add, _ -> plain "+"
  | Sub, _ -> plain "-"
  | Mul, _ -> plain "*"
  | Div, _ -> plain "/"
  | _ -> unsupported e.l "operator on %s" (show_ty at)

and conv fc (e : texpr) (a : texpr) target : r =
  let from = ts fc a.ty in
  let av = tmp fc from (expr fc a).c in
  let la = loc_args e.l in
  let tname = show_ty target in
  let fits lo hi = Printf.sprintf "if (%s) stn_conv_trap(%s, %s);" in
  ignore fits;
  match (repr from, repr target) with
  | TInt fk, TInt tk ->
      let c = ct fc target in
      (* range check by comparing as mathematical integers *)
      let fs = ikind_signed fk and ts_ = ikind_signed tk in
      let check =
        if fk = tk then None
        else if fs && ts_ then (if ikind_bits tk >= ikind_bits fk then None else Some (Printf.sprintf "(%s)(%s) != %s" (ct fc from) (Printf.sprintf "(%s)%s" c av) av))
        else if (not fs) && not ts_ then (if ikind_bits tk >= ikind_bits fk then None else Some (Printf.sprintf "%s > (%s)%s" av (ct fc from) (Printf.sprintf "UINT%d_MAX" (ikind_bits tk))))
        else if fs && not ts_ then
          Some (if ikind_bits tk >= ikind_bits fk then Printf.sprintf "%s < 0" av
                else Printf.sprintf "%s < 0 || (uint64_t)%s > (uint64_t)UINT%d_MAX" av av (ikind_bits tk))
        else (* unsigned to signed *)
          Some (Printf.sprintf "(uint64_t)%s > (uint64_t)INT%d_MAX" av (ikind_bits tk))
      in
      (match check with Some ck -> line fc "if (%s) stn_conv_trap(%s, %s);" ck (c_string tname) la | None -> ());
      { c = Printf.sprintf "((%s)%s)" c av; owned = false }
  | (TBool | TChar), TInt tk ->
      if ikind_bits tk < 32 && repr from = TChar then
        line fc "if ((uint64_t)%s > (uint64_t)%s) stn_conv_trap(%s, %s);" av
          (if ikind_signed tk then Printf.sprintf "INT%d_MAX" (ikind_bits tk) else Printf.sprintf "UINT%d_MAX" (ikind_bits tk)) (c_string tname) la;
      { c = Printf.sprintf "((%s)%s)" (ct fc target) av; owned = false }
  | TInt _, (TFloat | TF32) | (TFloat | TF32 | TBool | TChar), (TFloat | TF32) -> { c = Printf.sprintf "((%s)%s)" (ct fc target) av; owned = false }
  | (TFloat | TF32), TInt tk ->
      let lo = if ikind_signed tk then Printf.sprintf "(double)INT%d_MIN" (ikind_bits tk) else "0.0" in
      let hi = if tk = U64 then "18446744073709551616.0" else if ikind_signed tk then Printf.sprintf "((double)INT%d_MAX + 1.0)" (ikind_bits tk) else Printf.sprintf "((double)UINT%d_MAX + 1.0)" (ikind_bits tk) in
      line fc "if (!(trunc(%s) >= %s && trunc(%s) < %s)) stn_conv_trap(%s, %s);" av lo av hi (c_string tname) la;
      { c = Printf.sprintf "((%s)%s)" (ct fc target) av; owned = false }
  | TInt _, TChar ->
      line fc "stn_check_char((int64_t)%s, %s);" av la;
      { c = Printf.sprintf "((uint32_t)%s)" av; owned = false }
  | _ -> { c = Printf.sprintf "((%s)%s)" (ct fc target) av; owned = false }

and try_ fc t (a : texpr) : r =
  let st = fc.st in
  let res = fresh st "_r" and ev = fresh st "_te" and lbl = fresh st "try_fail" and done_ = fresh st "try_done" in
  let ok_t, err_t = match repr t with TNamed ("Result", [ o; e ]) -> (o, e) | _ -> assert false in
  line fc "%s %s; StnError %s;" (ct fc t) res ev;
  line fc "{";
  fc.ind <- fc.ind + 1;
  push fc (FTry (lbl, ev));
  push fc FStmt;
  let x = expr fc a in
  let v = tmp fc ok_t (own fc x ok_t) in
  pop fc;
  fc.frames <- List.tl fc.frames;
  let okv = construct fc t 0 [ v ] in
  line fc "%s = %s;" res okv.c;
  line fc "goto %s;" done_;
  fc.ind <- fc.ind - 1;
  line fc "}";
  line fc "%s:;" lbl;
  line fc "{";
  fc.ind <- fc.ind + 1;
  let payload =
    match repr err_t with
    | TErr _ -> ev
    | _ ->
        ignore (err_id st err_t);
        let p = tmp fc err_t (dup_expr st err_t (err_val st err_t ev)) in
        line fc "stn_error_drop(%s);" ev;
        p
  in
  let errv = construct fc t 1 [ payload ] in
  line fc "%s = %s;" res errv.c;
  fc.ind <- fc.ind - 1;
  line fc "}";
  line fc "%s:;" done_;
  { c = res; owned = true }

(* ---------- match (section 5.5) ---------- *)

and pat_test fc (t : ty) (p : tpat) (v : string) : string list * (string * var * ty) list =
  let st = fc.st in
  let t = ts fc t in
  match p with
  | TPWild -> ([], [])
  | TPVar var -> ([], [ (v, var, t) ])
  | TPLit (l, lt) -> (
      let x = (lit fc (ts fc lt) l).c in
      match repr t with
      | TStr -> ([ Printf.sprintf "stn_str_eq(%s, %s)" v x ], [])
      | TUnit -> ([], [])
      | _ -> ([ Printf.sprintf "(%s) == (%s)" v x ], []))
  | TPVariant (_, _, i, ps) ->
      let vinfo, fs = List.nth (variants st t) i in
      let tests = [ Printf.sprintf "%s == %d" (tag_of st t v) i ] in
      let sub = List.mapi (fun j (p, (_, ft)) -> pat_test fc ft p (variant_field st t vinfo j v)) (List.combine ps fs) in
      (tests @ List.concat_map fst sub, List.concat_map snd sub)
  | TPStruct (_, _, ps) ->
      let fs = struct_fields st t in
      let sub = List.map2 (fun p (n, ft) -> pat_test fc ft p (Printf.sprintf "(%s).%s" v (fname n))) ps fs in
      (List.concat_map fst sub, List.concat_map snd sub)
  | TPTuple ps -> (
      match repr t with
      | TTuple ts_ ->
          let sub = List.mapi (fun i (p, ft) -> pat_test fc ft p (Printf.sprintf "(%s).f%d" v i)) (List.combine ps ts_) in
          (List.concat_map fst sub, List.concat_map snd sub)
      | _ -> ([], []))
  | TPErrType (et, p) ->
      let et = ts fc et in
      let id = err_id st et in
      let tests, binds = pat_test fc et p (err_val st et v) in
      (Printf.sprintf "(%s).type_id == %d" v id :: tests, binds)

and bind_pattern fc binds =
  List.iter
    (fun (path, (var : var), t) ->
      let n = var_name var in
      line fc "%s %s = %s;" (cty fc.st t) n path;
      Hashtbl.replace fc.vars var.vid (VDirect n))
    binds

and match_ fc t (s : texpr) arms : r =
  let st = fc.st in
  (* The arms bind borrowed views into the scrutinee, so it must outlive the match even
     when an arm overwrites the place it was read from: hold a reference of our own. *)
  let sv = tmp fc s.ty (own fc (expr fc s) s.ty) in
  if rc fc s.ty then own_in fc sv s.ty;
  let has_value = match repr t with TUnit | TNever -> false | _ -> true in
  let res = fresh st "_r" and endl = fresh st "match_end" in
  if has_value then line fc "%s %s;" (ct fc t) res;
  List.iter
    (fun arm ->
      let tests, binds = pat_test fc s.ty arm.pat sv in
      let test = if tests = [] then "1" else String.concat " && " tests in
      line fc "if (%s) {" test;
      fc.ind <- fc.ind + 1;
      bind_pattern fc binds;
      let body () =
        if has_value then assign_into fc res arm.body t else discard fc arm.body;
        line fc "goto %s;" endl
      in
      (match arm.guard with
       | Some g ->
           let gv = cond fc g in
           line fc "if (%s) {" gv;
           fc.ind <- fc.ind + 1;
           body ();
           fc.ind <- fc.ind - 1;
           line fc "}"
       | None -> body ());
      fc.ind <- fc.ind - 1;
      line fc "}")
    arms;
  line fc "stn_trap(\"unreachable\", %s, \"no match arm applied\");" (loc_args s.l);
  line fc "%s:;" endl;
  { c = (if has_value then res else "0"); owned = has_value }

(* ---------- closures (section 13) ---------- *)

and closure fc (lam : lambda) : string =
  let st = fc.st in
  let name = fresh st ("clo_" ^ c_ident lam.lname ^ "_") in
  let ft = { lam.lfn with fps = List.map (fun (m, t) -> (m, ts fc t)) lam.lfn.fps; fret = ts fc lam.lfn.fret } in
  let caps = lam.lcaps in
  let cap_field (v : var) = Printf.sprintf "c%d_%s" v.vid (c_ident v.vname) in
  let cap_ctype (v : var) =
    if is_cell fc v then cell_type st (ts fc v.vty) ^ "*" else ct fc v.vty
  in
  (* the closure object type *)
  pr st.typedefs "typedef struct { StnClosure base; %s } %s_t;\n"
    (String.concat " " (List.map (fun v -> cap_ctype v ^ " " ^ cap_field v ^ ";") caps)) name;
  pr st.protos "static void %s_release(void* p);\n" name;
  pr st.helpers "static void %s_release(void* p) { %s_t* self = (%s_t*)p; (void)self; %s stn_free(p); }\n" name name name
    (String.concat " "
       (List.map
          (fun v ->
            if is_cell fc v then Printf.sprintf "stn_drop(self->%s, release_%s);" (cap_field v) (cell_type st (ts fc v.vty))
            else if rc fc v.vty then drop_stmt st (ts fc v.vty) ("self->" ^ cap_field v)
            else "")
          caps));
  (* the code *)
  let b = Buffer.create 1024 in
  let params = List.map (fun (v : var) -> (v, (match v.vkind with VParam m -> m | VLocal -> MBorrow))) lam.lparams in
  let header =
    Printf.sprintf "static uint8_t %s_code(StnClosure* self_, %s* _out, StnError* _err%s)" name (cty st ft.fret)
      (String.concat "" (List.map (fun (v, m) -> ", " ^ param_decl st m (ts fc v.vty) (var_name v)) params))
  in
  pr st.protos "%s;\n" header;
  let fc' = { st; b; ind = 1; sub = fc.sub; frames = []; can_fail = true; ret = ft.fret; vars = Hashtbl.create 16; self_struct = Some name; cached = Hashtbl.create 4; lend = None } in
  List.iter
    (fun (v : var) ->
      if is_cell fc v then Hashtbl.replace fc'.vars v.vid (VCapCell (Printf.sprintf "((%s_t*)self_)->%s" name (cap_field v), ts fc v.vty))
      else Hashtbl.replace fc'.vars v.vid (VCap (Printf.sprintf "((%s_t*)self_)->%s" name (cap_field v))))
    caps;
  pr b "%s {\n" header;
  push fc' FFun;
  List.iter
    (fun (v, m) ->
      match m with
      | MMut -> Hashtbl.replace fc'.vars v.vid (VPtr (var_name v))
      | MTake -> Hashtbl.replace fc'.vars v.vid (VDirect (var_name v)); if rc fc' v.vty then own_in fc' (var_name v) v.vty
      | MBorrow -> Hashtbl.replace fc'.vars v.vid (VDirect (var_name v)))
    params;
  let x = expr fc' lam.lbody in
  let rv = own fc' x lam.lbody.ty in
  let rv = if repr (ts fc' lam.lbody.ty) = TNever then "0" else rv in
  let rt = tmp fc' ft.fret rv in
  pop fc';
  line fc' "*_out = %s;" rt;
  line fc' "return 0;";
  pr b "}\n";
  Buffer.add_buffer st.funcs b;
  (* build the object *)
  let o = fresh st "_clo" in
  line fc "%s_t* %s = (%s_t*)stn_alloc(sizeof(%s_t));" name o name name;
  line fc "%s->base.code = (void*)%s_code; %s->base.release = %s_release;" o name o name;
  List.iter
    (fun (v : var) ->
      if is_cell fc v then begin
        let p = cell_ptr fc v in
        line fc "stn_dup(%s); %s->%s = %s;" p o (cap_field v) p
      end else line fc "%s->%s = %s;" o (cap_field v) (dup_expr st (ts fc v.vty) (var_read fc v)))
    caps;
  Printf.sprintf "((StnClosure*)%s)" o

(* ---------- places ---------- *)

(* an lvalue for a place, making every array on the way unshared (section 4.5) *)
and place_lvalue ?(write = true) fc (p : place) : string =
  let root () =
    match p.via with
    | Some call -> (expr fc call).c
    | None ->
    match Hashtbl.find_opt fc.vars p.root.vid with
    | Some (VDirect n) -> n
    | Some (VPtr n) -> "(*" ^ n ^ ")"
    | Some (VCell (n, _)) | Some (VCapCell (n, _)) -> n ^ "->value"
    | Some (VCap n) -> n
    | None -> failwith "cgen: unbound place root"
  in
  let rec go lv (t : ty) = function
    | [] -> lv
    | PField (_, f) :: rest ->
        let ft = List.assoc f (struct_fields fc.st t) in
        go (Printf.sprintf "%s.%s" lv (fname f)) ft rest
    | PTupleIx i :: rest ->
        let ft = match repr t with TTuple ts_ -> List.nth ts_ i | _ -> assert false in
        go (Printf.sprintf "%s.f%d" lv i) ft rest
    | PIndex ix :: rest ->
        let et = match repr t with TArray et -> et | _ -> assert false in
        let iv = tmp fc (TInt IInt) (expr fc ix).c in
        if write then line fc "stn_array_make_unique(&%s);" lv;
        go (Printf.sprintf "((%s*)(%s)->data)[stn_index(%s, stn_len(%s), %s)]" (cty fc.st et) lv iv lv (loc_args ix.l)) et rest
  in
  match ((if p.via = None then Hashtbl.find_opt fc.cached p.root.vid else None), p.path) with
  | Some (d, n), PIndex ix :: rest ->
      (* hoisted for this loop: already unshared, and its data and length are fixed *)
      let et = match repr (ts fc p.root.vty) with TArray et -> et | _ -> assert false in
      let iv = tmp fc (TInt IInt) (expr fc ix).c in
      go (Printf.sprintf "%s[stn_index(%s, %s, %s)]" d iv n (loc_args ix.l)) et rest
  | _ ->
      let start = root () in
      let t0 = match p.via with Some call -> ts fc call.ty | None -> ts fc p.root.vty in
      go start t0 p.path

(* a place expression as a place: a variable or a lend call, then fields and elements *)
and to_place fc (e : texpr) : place option =
  match e.e with
  | XVar v -> Some { root = v; via = None; path = []; pty = e.ty }
  | XField (b, i, f) -> Option.map (fun p -> { p with path = p.path @ [ PField (i, f) ]; pty = e.ty }) (to_place fc b)
  | XTupleGet (b, i) -> Option.map (fun p -> { p with path = p.path @ [ PTupleIx i ]; pty = e.ty }) (to_place fc b)
  | XIndex (b, i) -> Option.map (fun p -> { p with path = p.path @ [ PIndex i ]; pty = e.ty }) (to_place fc b)
  | XCall (_, args, _) when lend_sig fc e <> None -> (
      let lent = match List.find_opt (fun a -> a.amode = MMut) args with Some a -> Some a | None -> (match args with a :: _ -> Some a | [] -> None) in
      match Option.bind lent (fun a -> to_place fc a.a) with
      | Some base -> Some { root = base.root; via = Some e; path = []; pty = e.ty }
      | None -> None)
  | _ -> None

and place_lvalue_of_expr fc (e : texpr) : string =
  match to_place fc e with
  | Some p ->
      (match cell_root fc e with
       | Some (c, l) -> line fc "if (%s->busy) stn_trap(\"shared cell busy\", %s, \"a shared cell was accessed while it was lent out\");" c (loc_args l)
       | None -> ());
      place_lvalue fc p
  | None ->
      (* not a place (cannot happen after type checking): pass a temporary *)
      tmp fc e.ty (own fc (expr fc e) e.ty)

(* the cell behind a place expression, with the location of its root *)
and cell_root fc (e : texpr) : (string * Syntax.loc) option =
  match e.e with
  | XVar v -> if is_cell fc v then Some (cell_ptr fc v, e.l) else None
  | XField (b, _, _) | XTupleGet (b, _) | XIndex (b, _) -> cell_root fc b
  | _ -> None

(* a long access (section 13.3): the cell stays busy until the enclosing frame ends *)
and hold_busy fc (e : texpr) =
  match cell_root fc e with
  | Some (c, _) ->
      line fc "%s->busy = 1;" c;
      (match fc.frames with f :: _ -> f.owned <- (c, TNamed ("__unbusy", [])) :: f.owned | [] -> ())
  | None -> ()

(* ---------- loops ---------- *)

and loop_over fc (src : titer) (p : tpat) (body : unit -> unit) =
  let st = fc.st in
  match src with
  | IRange (a, b) ->
      let it = ts fc a.ty in
      let lo = tmp fc it (expr fc a).c and hi = tmp fc it (expr fc b).c in
      let i = fresh st "_i" in
      line fc "for (%s %s = %s; %s < %s; %s++) {" (ct fc it) i lo i hi i;
      fc.ind <- fc.ind + 1;
      push fc FLoop;
      let tests, binds = pat_test fc it p i in
      bind_pattern fc binds;
      ignore tests;
      push fc FScope;
      body ();
      pop fc;
      pop fc;
      fc.ind <- fc.ind - 1;
      line fc "}"
  | IArray (a, MMut) -> (
      match p with
      | TPVar var ->
          push fc FScope;
          let lv = place_lvalue_of_expr fc a in
          hold_busy fc a;
          let et = match repr (ts fc a.ty) with TArray et -> et | _ -> assert false in
          let i = fresh st "_i" in
          line fc "for (int64_t %s = 0; %s < stn_len(%s); %s++) {" i i lv i;
          fc.ind <- fc.ind + 1;
          push fc FLoop;
          line fc "stn_array_make_unique(&%s);" lv;
          let n = var_name var in
          line fc "%s* %s = &((%s*)(%s)->data)[%s];" (cty st et) n (cty st et) lv i;
          Hashtbl.replace fc.vars var.vid (VPtr n);
          push fc FScope;
          body ();
          pop fc;
          pop fc;
          fc.ind <- fc.ind - 1;
          line fc "}";
          pop fc
      | _ -> unsupported a.l "for ... in mut with a pattern")
  | IArray (a, _) ->
      let et = match repr (ts fc a.ty) with TArray et -> et | _ -> assert false in
      (* the loop holds its own reference, so the body may change the variable freely *)
      let av = tmp fc a.ty (own fc (expr fc a) a.ty) in
      own_in fc av a.ty;
      let i = fresh st "_i" in
      line fc "for (int64_t %s = 0; %s < stn_len(%s); %s++) {" i i av i;
      fc.ind <- fc.ind + 1;
      push fc FLoop;
      let x = tmp fc et (Printf.sprintf "((%s*)%s->data)[%s]" (cty st et) av i) in
      let _, binds = pat_test fc et p x in
      bind_pattern fc binds;
      push fc FScope;
      body ();
      pop fc;
      pop fc;
      fc.ind <- fc.ind - 1;
      line fc "}"

(* ---------- hoisting arrays out of loops ---------- *)

(* A loop whose body uses an array variable only through element reads, element writes
   and len cannot change that array's identity or length: nothing else can reach a
   local or mut parameter that is not a shared cell. The array is made unshared once
   before the loop (if the body writes it), and its data pointer and length are read
   into locals, so the bounds checks compare against a value the C compiler knows is
   fixed. Every check stays. *)
and with_hoisted fc (body : texpr list) (k : unit -> unit) =
  let cands = Hashtbl.create 4 in
  List.iter (iter_vars (fun (v : var) ->
      match (repr (ts fc v.vty), Hashtbl.find_opt fc.vars v.vid) with
      | TArray _, Some (VDirect _ | VPtr _) when not (Hashtbl.mem fc.cached v.vid) -> Hashtbl.replace cands v.vid v
      | _ -> ())) body;
  let added = ref [] in
  Hashtbl.iter
    (fun _ (v : var) ->
      match hoistable v body with
      | Some writes ->
          let lv = var_read fc v in
          let et = match repr (ts fc v.vty) with TArray et -> et | _ -> assert false in
          if writes then line fc "stn_array_make_unique(&%s);" lv;
          let d = fresh fc.st "_d" and n = fresh fc.st "_n" in
          line fc "%s* %s = (%s*)(%s)->data; int64_t %s = stn_len(%s);" (ct fc et) d (ct fc et) lv n lv;
          Hashtbl.replace fc.cached v.vid (d, n);
          added := v.vid :: !added
      | None -> ())
    cands;
  k ();
  List.iter (Hashtbl.remove fc.cached) !added

and iter_vars (f : var -> unit) (e : texpr) = walk_texpr (fun (x : texpr) -> match x.e with XVar v -> f v | _ -> ()) (fun _ -> ()) e

(* visit every expression and statement *)
and walk_texpr (fe : texpr -> unit) (fs : tstmt -> unit) (e : texpr) =
  let we = walk_texpr fe fs in
  let wit = function IRange (a, b) -> we a; we b | IArray (a, _) -> we a in
  let rec ws (s : tstmt) =
    fs s;
    match s.st with
    | SLet (_, e) | SVar (_, e) | SExpr e | SReturn e | SAssert (e, _) | SAssertFails (_, e) | SCheck e -> we e
    | SAssign (p, e) -> List.iter (function PIndex i -> we i | _ -> ()) p.path; we e
    | SBreak | SContinue -> ()
    | SWhile (c, b) -> we c; we b
    | SFor (_, it, b) -> wit it; we b
    | SLocalFn (_, lam) -> we lam.lbody
    | SLend e -> we e
  in
  fe e;
  match e.e with
  | XLit _ | XNone | XVar _ | XFnRef _ -> ()
  | XFStr es | XTuple es | XArray es | XStruct (_, _, es) | XVariant (_, _, _, es) -> List.iter we es
  | XCall (cl, args, _) -> (match cl with CClosure f -> we f | _ -> ()); List.iter (fun a -> we a.a) args
  | XField (b, _, _) | XTupleGet (b, _) | XNeg b | XNot b | XTry b | XConv b | XFail b | XPack b -> we b
  | XIndex (a, b) | XBin (_, a, b) -> we a; we b
  | XSlice (a, b, c) | XIf (a, b, c) -> we a; we b; we c
  | XBlock (ss, v) -> List.iter ws ss; we v
  | XMatch (s, arms) -> we s; List.iter (fun a -> Option.iter we a.guard; we a.body) arms
  | XLambda lam -> we lam.lbody
  | XComp (b, cs) -> we b; List.iter (fun cp -> wit cp.csrc; Option.iter we cp.ccond) cs

(* Some writes when [v] is used only through elements and len in [body] *)
and hoistable (v : var) (body : texpr list) : bool option =
  let writes = ref false in
  let is_v (e : texpr) = match e.e with XVar w -> w.vid = v.vid | _ -> false in
  let rec ok (e : texpr) : bool =
    match e.e with
    | XVar w -> w.vid <> v.vid
    | XIndex (a, i) when is_v a -> ok i
    | XCall (CBuiltin ("len@Array", _), [ a ], _) when is_v a.a -> true
    | XLambda lam -> (not (List.exists (fun (c : var) -> c.vid = v.vid) lam.lcaps)) && ok lam.lbody
    | XCall (cl, args, _) ->
        (* an element passed as mut may be written *)
        List.iter (fun a -> if a.amode = MMut && mentions a.a then writes := true) args;
        (match cl with CClosure f -> ok f | _ -> true) && List.for_all (fun a -> ok a.a) args
    | _ -> children_ok e
  and mentions (e : texpr) = let m = ref false in iter_vars (fun w -> if w.vid = v.vid then m := true) e; !m
  and children_ok (e : texpr) : bool =
    let good = ref true in
    let first = ref true in
    (* check the immediate children only; ok recurses itself *)
    let visit_child (c : texpr) = if not (ok c) then good := false in
    let wit = function IRange (a, b) -> visit_child a; visit_child b | IArray (a, _) -> visit_child a in
    let rec st (s : tstmt) =
      match s.st with
      | SLet (_, e) | SVar (_, e) | SExpr e | SReturn e | SAssert (e, _) | SAssertFails (_, e) | SCheck e -> visit_child e
      | SAssign (p, e) ->
          if p.root.vid = v.vid then (match p.path with PIndex _ :: _ -> writes := true | _ -> good := false);
          List.iter (function PIndex i -> visit_child i | _ -> ()) p.path;
          visit_child e
      | SBreak | SContinue -> ()
      | SWhile (c, b) -> visit_child c; visit_child b
      | SFor (_, it, b) -> wit it; visit_child b
      | SLend e -> visit_child e
      | SLocalFn (_, lam) ->
          if List.exists (fun (c : var) -> c.vid = v.vid) lam.lcaps then good := false;
          visit_child lam.lbody
    in
    ignore first;
    (match e.e with
     | XLit _ | XNone | XVar _ | XFnRef _ | XLambda _ | XCall _ -> ()
     | XFStr es | XTuple es | XArray es | XStruct (_, _, es) | XVariant (_, _, _, es) -> List.iter visit_child es
     | XField (b, _, _) | XTupleGet (b, _) | XNeg b | XNot b | XTry b | XConv b | XFail b | XPack b -> visit_child b
     | XIndex (a, b) | XBin (_, a, b) -> visit_child a; visit_child b
     | XSlice (a, b, c) | XIf (a, b, c) -> visit_child a; visit_child b; visit_child c
     | XBlock (ss, x) -> List.iter st ss; visit_child x
     | XMatch (s, arms) -> visit_child s; List.iter (fun a -> Option.iter visit_child a.guard; visit_child a.body) arms
     | XComp (b, cs) -> visit_child b; List.iter (fun cp -> wit cp.csrc; Option.iter visit_child cp.ccond) cs);
    !good
  in
  if v.vcell then None else if List.for_all ok body then Some !writes else None

(* ---------- statements ---------- *)

and declare_var fc (v : var) (init : string) =
  let st = fc.st in
  let n = var_name v in
  let t = ts fc v.vty in
  if v.vcell then begin
    let cn = cell_type st t in
    line fc "%s* %s = (%s*)stn_alloc(sizeof(%s)); %s->busy = 0; %s->value = %s;" cn n cn cn n n init;
    Hashtbl.replace fc.vars v.vid (VCell (n, t));
    match fc.frames with
    | f :: _ -> f.owned <- (Printf.sprintf "%s" n, TNamed ("__cell", [ t ])) :: f.owned
    | [] -> ()
  end else begin
    line fc "%s %s = %s;" (cty st t) n init;
    Hashtbl.replace fc.vars v.vid (VDirect n);
    if needs_rc st t then own_in fc n t
  end

and stmt fc (s : tstmt) =
  let st = fc.st in
  push fc FStmt;
  (match s.st with
   | SLet (TPVar v, e) | SVar (v, e) ->
       let x = expr fc e in
       (* evaluate fully before the statement's temporaries are released *)
       let init = tmp fc e.ty (own fc x e.ty) in
       (* declared in the enclosing scope, not the statement frame *)
       let f = List.hd fc.frames in
       fc.frames <- List.tl fc.frames;
       emit_drops fc f;
       declare_var fc v init;
       fc.frames <- { fk = FStmt; owned = [] } :: fc.frames
   | SLet (p, e) ->
       let x = expr fc e in
       let init = own fc x e.ty in
       let f = List.hd fc.frames in
       fc.frames <- List.tl fc.frames;
       let n = tmp fc e.ty init in
       emit_drops fc f;
       own_in fc n e.ty;
       let _, binds = pat_test fc e.ty p n in
       bind_pattern fc binds;
       fc.frames <- { fk = FStmt; owned = [] } :: fc.frames
   | SAssign (p, e) ->
       let x = expr fc e in
       let nv = tmp fc p.pty (own fc x e.ty) in
       if is_cell fc p.root then begin
         let c = cell_ptr fc p.root in
         line fc "if (%s->busy) stn_trap(\"shared cell busy\", %s, \"a shared cell was assigned while it was lent out\");" c (loc_args s.sl)
       end;
       let lv = place_lvalue fc p in
       if rc fc p.pty then line fc "%s" (drop_stmt st (ts fc p.pty) lv);
       line fc "%s = %s;" lv nv
   | SExpr e -> discard_value fc e
   | SReturn e ->
       let x = expr fc e in
       let v = if repr (ts fc e.ty) = TNever then "0" else own fc x e.ty in
       let rv = tmp fc fc.ret v in
       drop_until fc (fun _ -> false);
       if fc.can_fail then (line fc "*_out = %s;" rv; line fc "return 0;") else line fc "return %s;" rv
   | SBreak ->
       drop_until fc (fun f -> f.fk = FLoop);
       line fc "break;"
   | SContinue ->
       drop_until fc (fun f -> f.fk = FLoop);
       line fc "continue;"
   | SWhile (c, body) ->
       with_hoisted fc [ c; body ] @@ fun () ->
       line fc "for (;;) {";
       fc.ind <- fc.ind + 1;
       push fc FLoop;
       let cv = cond fc c in
       line fc "if (!%s) break;" cv;
       push fc FScope;
       discard fc body;
       pop fc;
       pop fc;
       fc.ind <- fc.ind - 1;
       line fc "}"
   | SFor (p, src, body) -> with_hoisted fc [ body ] (fun () -> loop_over fc src p (fun () -> discard fc body))
   | SAssert (e, _) ->
       let cv = cond fc e in
       line fc "if (!%s) stn_trap(\"assertion failed\", %s, \"assert\");" cv (loc_args s.sl)
   | SAssertFails _ -> unsupported s.sl "assert_fails outside starnite test"
   | SCheck e ->
       let cv = cond fc e in
       line fc "if (!%s) stn_trap(\"check failed\", %s, \"the checked condition is false\");" cv (loc_args s.sl)
   | SLend e ->
       (* for lend mut, any copy section 4.5 needs happens before the pointer is taken *)
       let write = fc.lend = Some true in
       let lv = match to_place fc e with Some p -> place_lvalue ~write fc p | None -> (expr fc e).c in
       let pv = fresh st "_lp" in
       line fc "%s* %s = &(%s);" (ct fc e.ty) pv lv;
       drop_until fc (fun _ -> false);
       line fc "return %s;" pv
   | SLocalFn (v, lam) ->
       let c = closure fc lam in
       let f = List.hd fc.frames in
       fc.frames <- List.tl fc.frames;
       emit_drops fc f;
       declare_var fc v c;
       fc.frames <- { fk = FStmt; owned = [] } :: fc.frames);
  pop fc

(* ---------- built-in functions ---------- *)

and builtin fc (e : texpr) name tys (targs : targ list) convs : r =
  let st = fc.st in
  let t = ts fc e.ty in
  let la = loc_args e.l in
  let arg i = List.nth targs i in
  let b i = borrow fc (expr fc (arg i).a) (arg i).a.ty in
  let o i = tmp fc (arg i).a.ty (own fc (expr fc (arg i).a) (arg i).a.ty) in
  let m i = place_lvalue_of_expr fc (arg i).a in
  let unit_ () = { c = "0"; owned = false } in
  let value c = { c; owned = false } in
  let owned c = { c = tmp fc t c; owned = true } in
  let elt () = match tys with [ x ] -> x | _ -> TUnit in
  match name with
  | "print@Str" -> line fc "stn_print(%s);" (b 0); unit_ ()
  | "read_line@" ->
      let s = fresh st "_s" in
      line fc "StnStr %s;" s;
      let ok = tmp fc TBool (Printf.sprintf "stn_read_line(&%s)" s) in
      let res = fresh st "_r" in
      line fc "%s %s;" (ct fc t) res;
      line fc "if (%s) {" ok;
      let sv = construct fc t 1 [ s ] in
      line fc "  %s = %s;" res sv.c;
      line fc "} else {";
      let nv = construct fc t 0 [] in
      line fc "  %s = %s;" res nv.c;
      line fc "}";
      { c = res; owned = true }
  | "clock_ns@" -> value "stn_clock_ns()"
  | "len@Array" -> (
      match (arg 0).a.e with
      | XVar v when Hashtbl.mem fc.cached v.vid -> value (snd (Hashtbl.find fc.cached v.vid))
      | _ -> value (Printf.sprintf "stn_len(%s)" (b 0)))
  | "len@Str" -> value (Printf.sprintf "(%s)->len" (b 0))
  | "push@Array" ->
      let lv = m 0 in
      let x = o 1 in
      line fc "STN_PUSH(&%s, %s, %s);" lv (cty st (elt ())) x;
      unit_ ()
  | "pop@Array" ->
      let lv = m 0 in
      let x = fresh st "_x" in
      line fc "%s %s;" (cty st (elt ())) x;
      let ok = tmp fc TBool (Printf.sprintf "stn_array_pop(&%s, &%s)" lv x) in
      let res = fresh st "_r" in
      line fc "%s %s;" (ct fc t) res;
      line fc "if (%s) {" ok;
      let sv = construct fc t 1 [ x ] in
      line fc "  %s = %s;" res sv.c;
      line fc "} else {";
      let nv = construct fc t 0 [] in
      line fc "  %s = %s;" res nv.c;
      line fc "}";
      { c = res; owned = true }
  | "insert@Array" ->
      let lv = m 0 in
      let i = tmp fc (TInt IInt) (expr fc (arg 1).a).c in
      let x = o 2 in
      line fc "stn_array_insert(&%s, %s, &%s, %s);" lv i x la;
      unit_ ()
  | "remove@Array" ->
      let lv = m 0 in
      let i = tmp fc (TInt IInt) (expr fc (arg 1).a).c in
      let x = fresh st "_x" in
      line fc "%s %s;" (cty st t) x;
      line fc "stn_array_remove(&%s, %s, &%s, %s);" lv i x la;
      { c = x; owned = true }
  | "clear@Array" -> line fc "stn_array_clear(&%s);" (m 0); unit_ ()
  | "extend@Array" ->
      let lv = m 0 in
      let ys = b 1 in
      line fc "stn_array_extend(&%s, %s);" lv ys;
      unit_ ()
  | "filled@Int" ->
      let n = tmp fc (TInt IInt) (expr fc (arg 0).a).c in
      let x = b 1 in
      let xt = tmp fc (elt ()) x in
      owned (Printf.sprintf "stn_array_filled(%s, %s, &%s, %s)" (elem_ops st (elt ())) n xt la)
  | "copy@T" ->
      let x = expr fc (arg 0).a in
      { c = tmp fc t (own fc x t); owned = true }
  | "unreachable@Str" ->
      line fc "stn_trap(\"unreachable\", %s, (%s)->data);" la (b 0);
      let res = fresh st "_r" in
      line fc "%s %s;" (ct fc t) res;
      line fc "memset(&%s, 0, sizeof %s);" res res;
      { c = res; owned = false }
  | "chars@Str" -> owned (Printf.sprintf "stn_str_chars(%s, %s)" (b 0) (elem_ops st TChar))
  | "split@Str" -> let s = b 0 in let sep = b 1 in owned (Printf.sprintf "stn_str_split(%s, %s, %s, %s)" s sep (elem_ops st TStr) la)
  | "join@Array" -> let xs = b 0 in let sep = b 1 in owned (Printf.sprintf "stn_str_join(%s, %s)" xs sep)
  | "trim@Str" -> owned (Printf.sprintf "stn_str_trim(%s)" (b 0))
  | "contains@Str" -> let s = b 0 in let x = b 1 in value (Printf.sprintf "stn_str_contains(%s, %s)" s x)
  | "starts_with@Str" -> let s = b 0 in let x = b 1 in value (Printf.sprintf "stn_str_starts_with(%s, %s)" s x)
  | "ends_with@Str" -> let s = b 0 in let x = b 1 in value (Printf.sprintf "stn_str_ends_with(%s, %s)" s x)
  | "repeat@Str" -> let s = b 0 in let n = tmp fc (TInt IInt) (expr fc (arg 1).a).c in owned (Printf.sprintf "stn_str_repeat(%s, %s, %s)" s n la)
  | "parse_int@Str" | "parse_float@Str" ->
      let s = b 0 in
      let is_int = name = "parse_int@Str" in
      let out = fresh st "_v" in
      line fc "%s %s;" (if is_int then "int64_t" else "double") out;
      let rcv = tmp fc (TInt IInt) (Printf.sprintf "%s(%s, &%s)" (if is_int then "stn_parse_int" else "stn_parse_float") s out) in
      let pe = TNamed ("ParseError", []) in
      ignore (err_id st pe);
      line fc "if (%s) {" rcv;
      fc.ind <- fc.ind + 1;
      let sd = tmp fc TStr (dup_expr st TStr s) in
      let inv = construct fc pe 0 [ sd ] in
      let oor = construct fc pe 1 [ sd ] in
      let ev = fresh st "_e" in
      line fc "StnError %s = errmake_%s(%s == 1 ? %s : %s);" ev (mangle pe) rcv inv.c oor.c;
      apply_convs fc convs ev;
      propagate fc ev;
      fc.ind <- fc.ind - 1;
      line fc "}";
      value out
  | "sqrt@Float" | "sin@Float" | "cos@Float" | "tan@Float" | "exp@Float" | "log@Float" | "floor@Float" | "ceil@Float" ->
      let f = String.sub name 0 (String.index name '@') in
      value (Printf.sprintf "%s(%s)" f (b 0))
  | "abs@Float" -> value (Printf.sprintf "fabs(%s)" (b 0))
  | "pow@Float" -> let x = b 0 in let y = b 1 in value (Printf.sprintf "pow(%s, %s)" x y)
  | "abs@Int" ->
      let x = tmp fc (TInt IInt) (b 0) in
      line fc "if (%s == INT64_MIN) stn_overflow(%s);" x la;
      value (Printf.sprintf "(%s < 0 ? -%s : %s)" x x x)
  | _ -> unsupported e.l "built-in %s is not implemented in the C backend" name

(* ---------- function instances ---------- *)

let compile_instance st cname uname tys =
  let tf = Hashtbl.find st.prog.fns uname in
  let sg = tf.fsig in
  let sub = List.combine (List.map fst sg.stparams) tys in
  let ret = subst sub sg.sret in
  let can_fail = sig_can_fail sg in
  let params = List.map2 (fun (v : var) (m, _, t, _) -> (v, m, subst sub t)) tf.fparams sg.sparams in
  let plist = List.map (fun (v, m, t) -> param_decl st m t (var_name v)) params in
  let lend = sg.slend <> None in
  (* a lend function takes its borrowed parameters by address too, and returns a pointer *)
  let plist =
    if lend then List.map (fun (v, m, t) -> match m with MBorrow -> Printf.sprintf "%s* %s" (cty st t) (var_name v) | _ -> param_decl st m t (var_name v)) params
    else plist
  in
  let header =
    if lend then Printf.sprintf "static inline %s* %s(%s)" (cty st ret) cname (if plist = [] then "void" else String.concat ", " plist)
    else if can_fail then
      Printf.sprintf "static inline uint8_t %s(%s* _out, StnError* _err%s)" cname (cty st ret) (String.concat "" (List.map (fun p -> ", " ^ p) plist))
    (* inline is a hint: the C compiler weighs a body full of overflow checks as large,
       and small Starnite functions would otherwise stay calls in hot loops *)
    else Printf.sprintf "static inline %s %s(%s)" (cty st ret) cname (if plist = [] then "void" else String.concat ", " plist)
  in
  pr st.protos "%s;\n" header;
  let b = Buffer.create 4096 in
  let fc = { st; b; ind = 1; sub; frames = []; can_fail; ret; vars = Hashtbl.create 32; self_struct = None; cached = Hashtbl.create 4; lend = sg.slend } in
  pr b "%s {\n" header;
  push fc FFun;
  List.iter
    (fun (v, m, t) ->
      let n = var_name v in
      match m with
      | MMut -> Hashtbl.replace fc.vars v.vid (VPtr n)
      | MTake ->
          if v.vcell then begin
            let cn = cell_type st t in
            let c = n ^ "_cell" in
            line fc "%s* %s = (%s*)stn_alloc(sizeof(%s)); %s->busy = 0; %s->value = %s;" cn c cn cn c c n;
            Hashtbl.replace fc.vars v.vid (VCell (c, t));
            (List.hd fc.frames).owned <- (c, TNamed ("__cell", [ t ])) :: (List.hd fc.frames).owned
          end else begin
            Hashtbl.replace fc.vars v.vid (VDirect n);
            if needs_rc st t then own_in fc n t
          end
      | MBorrow ->
          if v.vcell then begin
            let cn = cell_type st t in
            let c = n ^ "_cell" in
            line fc "%s* %s = (%s*)stn_alloc(sizeof(%s)); %s->busy = 0; %s->value = %s;" cn c cn cn c c (dup_expr st t n);
            Hashtbl.replace fc.vars v.vid (VCell (c, t));
            (List.hd fc.frames).owned <- (c, TNamed ("__cell", [ t ])) :: (List.hd fc.frames).owned
          end else Hashtbl.replace fc.vars v.vid (if lend then VPtr n else VDirect n))
    params;
  if lend then begin
    (* every path ends in a lend statement, which returns; the checker proved it *)
    discard fc tf.fbody;
    pop fc;
    line fc "stn_trap(\"unreachable\", __FILE__, __LINE__, 0, \"a lend function ended without lend\");";
    pr b "}\n\n";
    Buffer.add_buffer st.funcs b
  end else begin
  push fc FStmt;
  let x = expr fc tf.fbody in
  let never = repr (ts fc tf.fbody.ty) = TNever in
  let rv = if never then "0" else own fc x tf.fbody.ty in
  let f = List.hd fc.frames in
  fc.frames <- List.tl fc.frames;
  let r = tmp fc ret rv in
  emit_drops fc f;
  pop fc;
  if can_fail then (line fc "*_out = %s;" r; line fc "return 0;") else line fc "return %s;" r;
  pr b "}\n\n";
  Buffer.add_buffer st.funcs b
  end

let () =
  request_instance :=
    fun st uname tys ->
      let cname = inst_name uname tys in
      if not (Hashtbl.mem st.instances cname) then begin
        Hashtbl.replace st.instances cname ();
        Queue.add (cname, uname, tys) st.queue
      end;
      cname

(* stn_show_error: the text of any error value, for main (section 5.4) *)
let emit_show_error st =
  let b = Buffer.create 1024 in
  pr b "static StnStr stn_show_error(StnError e) {\n  switch (e.type_id) {\n";
  let seen = Hashtbl.create 8 in
  let rec loop () =
    let pending = Hashtbl.fold (fun k (id, t) acc -> if Hashtbl.mem seen k then acc else (k, id, t) :: acc) st.errtypes [] in
    if pending <> [] then begin
      List.iter
        (fun (k, id, t) ->
          Hashtbl.replace seen k ();
          let fc = { st; b = Buffer.create 64; ind = 0; sub = []; frames = []; can_fail = false; ret = TStr; vars = Hashtbl.create 1; self_struct = None; cached = Hashtbl.create 4; lend = None } in
          pr b "    case %d: return %s;\n" id (show_call fc t (err_val st t "e")))
        pending;
      loop ()
    end
  in
  loop ();
  pr b "    default: return stn_str_new(\"error\", 5);\n  }\n}\n";
  b

let emit (prog : tprog) ~debug : string =
  let st = {
    prog; fwd = Buffer.create 1024; typedefs = Buffer.create 4096; boxed_bodies = Buffer.create 1024;
    protos = Buffer.create 4096; helpers = Buffer.create 4096; funcs = Buffer.create 16384;
    defined = Hashtbl.create 64; pending_boxed = Queue.create (); instances = Hashtbl.create 64;
    queue = Queue.create (); strlits = Hashtbl.create 64; errtypes = Hashtbl.create 8;
    layouts = Hashtbl.create 64; debug; counter = 0 }
  in
  let main_u = match prog.main with Some m -> m | None -> raise (Unsupported ("no main function", Syntax.noloc)) in
  let main_sg = (Hashtbl.find prog.fns main_u).fsig in
  let main_c = !request_instance st main_u [] in
  let rec drain () =
    if not (Queue.is_empty st.queue) then begin
      let cname, uname, tys = Queue.pop st.queue in
      compile_instance st cname uname tys;
      flush_boxed st;
      drain ()
    end
  in
  drain ();
  (* main's errors are printed, so their Show code must exist before the last drain *)
  List.iter (fun t -> ignore (err_id st t)) main_sg.seff.errs;
  pr st.protos "static StnStr stn_show_error(StnError e);\n";
  let show_err = emit_show_error st in
  drain ();
  let show_err2 = emit_show_error st in
  drain ();
  flush_boxed st;
  ignore show_err;
  let out = Buffer.create 65536 in
  pr out "/* Generated by the Starnite compiler. */\n";
  if debug then pr out "#define STN_DEBUG 1\n";
  pr out "#include <stdint.h>\n#include <stdio.h>\n#include <math.h>\n#include \"stn_runtime.h\"\n\n";
  Buffer.add_buffer out st.fwd;
  Buffer.add_buffer out st.typedefs;
  Buffer.add_buffer out st.boxed_bodies;
  pr out "\n";
  Buffer.add_buffer out st.protos;
  pr out "\n";
  Buffer.add_buffer out st.helpers;
  pr out "\n";
  Buffer.add_buffer out st.funcs;
  Buffer.add_buffer out show_err2;
  pr out "\nint main(void) {\n  stn_runtime_init();\n";
  if sig_can_fail main_sg then begin
    pr out "  StnUnit r; StnError e;\n  if (%s(&r, &e)) {\n" main_c;
    pr out "    StnStr s = stn_show_error(e);\n    fflush(stdout);\n";
    pr out "    stn_runtime_flush_for_error();\n    fprintf(stderr, \"error: %%.*s\\n\", (int)s->len, s->data);\n";
    pr out "    STN_STR_DROP(s); stn_error_drop(e);\n    stn_runtime_exit(1);\n  }\n"
  end else pr out "  %s();\n" main_c;
  pr out "  stn_runtime_exit(0);\n  return 0;\n}\n";
  Buffer.contents out
