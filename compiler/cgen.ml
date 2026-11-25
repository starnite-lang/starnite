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
  dps : (string * Buffer.t * (texpr -> unit)) option ref;   (* the destination of the function being generated as a loop (section 9.5), and its code *)
  reuse : (string * string * Buffer.t) list ref;   (* cells a match took apart, free for a constructor of the same type: C name, type, and the function's code, which a closure inside it does not share *)
  movable : texpr list ref;              (* the last occurrences of owned variables, which may move them (section 9.2) *)
  pinned : (int, unit) Hashtbl.t;        (* variables something borrows from to the end of their scope: never moved *)
  self_sliced : (int, unit) Hashtbl.t;   (* variables assigned a slice of themselves somewhere *)
  view_vars : (int, unit) Hashtbl.t;     (* variables that hold only views of strings that outlive them *)
  loops : (string, bool) Hashtbl.t;   (* whether a function loops, itself or through a call *)
  in_main : bool ref;                  (* the body being generated is main's *)
  entries : (string, string * string) Hashtbl.t;  (* entry wrappers that main calls: prototype and definition, by instance *)
  entry_defs : (string, string * string) Hashtbl.t;  (* the entry wrapper each instance could have *)
  errtypes : (string, int * ty) Hashtbl.t;
  layouts : (string, layout) Hashtbl.t;
  (* for the checks of noalloc and inplace functions (section 9.6, verify.ml) *)
  marking : bool ref;                    (* the function being generated is one of them *)
  cur : (Syntax.loc * string) ref;       (* the expression whose code is being written *)
  marks : (Buffer.t * int * Syntax.loc * string * bool) list ref;   (* where the code of each expression starts, and whether a loop of the program is around it *)
  explain : bool;                        (* --explain-copies: every function is recorded *)
  profile : bool;                        (* --profile-copies: generated code says which statement it is in *)
  excused : (Buffer.t * int * int) list ref;   (* code that runs only when a take argument is shared *)
  records : Verify.fn_record list ref;
  demoted : (string * int, unit) Hashtbl.t;   (* take parameters passed as read-only ones (section 9.4): function, position *)
  names : (string * string) list ref;    (* every function generated, and its name in the program *)
  debug : bool;
  mutable counter : int;
}

let fresh st prefix = st.counter <- st.counter + 1; Printf.sprintf "%s%d" prefix st.counter

let pr buf fmt = Printf.bprintf buf fmt

(* ---------- names ---------- *)

(* A name chosen in the program, as part of a C name. The C names join their parts with
   an underscore, so a name that has one, or that reads like a part of the scheme (Arr,
   Any, E, Tup2, anything starting with Fn or with a lower-case letter, ...), is spelled out instead: Zq, then the name with Z written ZZ and
   an underscore Zu, and a dot, which a module's path puts in the name of its types and traits, Zd.
   A plain name never starts with Z, so the two kinds cannot meet,
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
    "Zq" ^ String.concat "" (List.map (function 'Z' -> "ZZ" | '_' -> "Zu" | '.' -> "Zd" | c -> String.make 1 c) (List.init (String.length n) (String.get n)))

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
  | TArray _ | TFn _ -> 8
  | TStr | TErr _ | TAny _ -> 16
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
  | TNamed (("Map" | "Set"), _) -> true
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
  | TNamed (("Map" | "Set"), _) -> "StnMap*"
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
        (* boxed: one release function per type (section 11.2). The last field of each variant
           that holds a value of this same type is not released by a call: the function goes
           round again on it, so a long list is freed in constant stack (section 9.7). Fields
           before it are released by calls, so a tree still uses stack for its other branches. *)
        pr st.protos "static void release_%s(void* p);\n" m;
        let arms =
          String.concat " "
            (List.map
               (fun ((v : variant_info), fs) ->
                 let last_self =
                   List.fold_left (fun acc (i, (_, ft)) -> if repr ft = repr t || mangle ft = m then Some i else acc) None
                     (List.mapi (fun i f -> (i, f)) fs) in
                 let body =
                   String.concat " "
                     (List.mapi (fun i (_, ft) ->
                          let f = Printf.sprintf "x->u.%s.f%d" (c_ident v.vname_) i in
                          if Some i = last_self then Printf.sprintf "next = %s;" f
                          else if needs_rc st ft then drop_stmt st ft f else "") fs) in
                 if body = "" then "" else Printf.sprintf "case %d: %s break;" v.vindex body)
               (variants st t))
        in
        pr st.helpers
          "static void release_%s(void* p) { if (stn_release_enter(p, release_%s)) return; for (;;) { %s x = (%s)p; %s next = NULL; switch (x->h.tag) { %s default: break; } stn_free(p); if (next == NULL || ((uintptr_t)next & 1)) break; stn_header* h = (stn_header*)next; if (h->flags != 0) { stn_drop(next, release_%s); break; } STN_CHECK_HEADER(next); STN_COUNT_OP(); if (--h->rc != 0) break; if (--stn_release_left < 0) { stn_release_defer(next, release_%s); break; } p = next; } stn_release_leave(); }\n"
          m m c c c arms m m;
        pr st.helpers "static inline %s dup_%s(%s x) { stn_dup(x); return x; }\n" c m c;
        pr st.helpers "static inline void drop_%s(%s x) { stn_drop(x, release_%s); }\n" m c m
    | _ -> ()
  end

and dup_stmt st t e =
  match repr t with
  (* a Str is assigned its duplicate: the duplicate of a view is a buffer of its own *)
  | TStr -> Printf.sprintf "%s = stn_str_dup(%s);" e e
  | TArray _ | TFn _ | TNamed (("Map" | "Set"), _) -> Printf.sprintf "stn_dup(%s);" e
  | TErr _ -> Printf.sprintf "stn_error_dup(%s);" e
  | _ -> ensure_type st t; Printf.sprintf "%s = dup_%s(%s);" e (mangle t) e

and drop_stmt st t e =
  match repr t with
  | TNamed ("__cell", [ ct_ ]) -> Printf.sprintf "stn_drop(%s, release_cell_%s);" e (mangle ct_)
  | TNamed ("__unbusy", _) -> Printf.sprintf "%s->busy = 0;" e
  (* a cell that no constructor took over *)
  | TNamed ("__token", _) -> Printf.sprintf "if (%s) stn_free(%s);" e e
  | TNamed ("__array_length", _) -> e ^ ";"
  | TStr -> Printf.sprintf "STN_STR_DROP(%s);" e
  | TArray _ -> Printf.sprintf "stn_drop(%s, stn_array_release);" e
  | TNamed (("Map" | "Set"), _) -> Printf.sprintf "stn_drop(%s, stn_map_release);" e
  | TFn _ -> Printf.sprintf "stn_closure_drop(%s);" e
  | TErr _ -> Printf.sprintf "stn_error_drop(%s);" e
  | _ -> ensure_type st t; Printf.sprintf "drop_%s(%s);" (mangle t) e

let dup_expr st t e =
  if not (needs_rc st t) then e
  else
    match repr t with
    | TStr -> Printf.sprintf "stn_str_dup(%s)" e
    | TArray _ | TFn _ | TNamed (("Map" | "Set"), _) -> Printf.sprintf "(stn_dup(%s), %s)" e e
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
      let len = String.length s in
      if len <= 15 then begin
        (* inline: the bytes in two little-endian words, the length in the last byte *)
        let word lo hi =
          let w = ref 0L in
          for i = hi - 1 downto lo do
            let b = if i < len then Char.code s.[i] else if i = 15 then len else 0 in
            w := Int64.logor (Int64.shift_left !w 8) (Int64.of_int b)
          done;
          !w
        in
        (* and for a big-endian target, where the length is the first byte and the bytes follow it *)
        let big lo hi =
          let w = ref 0L in
          for i = lo to hi - 1 do
            let b = if i = 0 then len else if i - 1 < len then Char.code s.[i - 1] else 0 in
            w := Int64.logor (Int64.shift_left !w 8) (Int64.of_int b)
          done;
          !w
        in
        pr st.helpers "#define %s STN_STR_SHORT(UINT64_C(0x%016Lx), UINT64_C(0x%016Lx), UINT64_C(0x%016Lx), UINT64_C(0x%016Lx))\n"
          n (word 0 8) (word 8 16) (big 0 8) (big 8 16)
      end else begin
        pr st.helpers "static struct { stn_header h; int64_t len; char data[%d]; } %s_obj = { { 1, 0, STN_NOCOUNT, 0 }, %d, %s };\n"
          (len + 1) n len (c_string s);
        pr st.helpers "#define %s ((StnStr){ .ptr = %s_obj.data, .w1 = UINT64_C(%d) | STN_STR_HEAP_BIT })\n" n n len
      end;
      n

(* A release function for the object at p: drops is what it holds, as C statements. One that
   drops something goes in through stn_release_enter, so that releases cannot nest without bound
   (section 9.7). *)
let release_fn name before drops =
  if String.trim drops = "" then Printf.sprintf "static void %s(void* p) { %s stn_free(p); }\n" name before
  else Printf.sprintf "static void %s(void* p) { if (stn_release_enter(p, %s)) return; %s %s stn_free(p); stn_release_leave(); }\n" name name before drops

let err_id st t =
  let key = mangle t in
  match Hashtbl.find_opt st.errtypes key with
  | Some (id, _) -> id
  | None ->
      let id = Hashtbl.length st.errtypes + 1 in
      Hashtbl.replace st.errtypes key (id, t);
      let c = cty st t in
      pr st.protos "typedef struct { StnErrBox base; %s value; } errbox_%s;\nstatic StnError errmake_%s(%s v);\n" c key key c;
      Buffer.add_string st.helpers (release_fn ("errbox_release_" ^ key) ""
        (if needs_rc st t then drop_stmt st t (Printf.sprintf "((errbox_%s*)p)->value" key) else ""));
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
  natural_max : (int, int64) Hashtbl.t;  (* proven nonnegative range variables *)
  mutable unique_arrays : int list;
  mutable loop_indices : (texpr * string) list;
  mutable checked_ranges : (int * int64) list; (* array bounds proved at loop entry *)
  mutable unchecked_pops : (int * string) list;    (* exclusive arrays with enough elements for this loop *)
  lend : bool option;                          (* compiling a lend function (lend mut when Some true) *)
}

type r = { c : string; owned : bool }

let line fc fmt =
  Printf.ksprintf (fun s ->
      (* a profiled build gives each line of C the line of the statement it came from, which is
         how a count of copies finds its place in the program *)
      (if fc.st.profile then
         let (l : Syntax.loc), _ = !(fc.st.cur) in
         if l.line > 0 then Printf.bprintf fc.b "#line %d %s\n" l.line (c_string l.file));
      Buffer.add_string fc.b (String.make (2 * fc.ind) ' '); Buffer.add_string fc.b s; Buffer.add_char fc.b '\n') fmt

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

(* The address of a Str, for the runtime's string functions, which read a string where it already
   is. Passing an inline string by value would store its two words on the callee's stack just before
   its bytes are read back, and a read that spans both words cannot be forwarded from those stores.
   A name or an indexed element is used in place; anything else is held in a temporary first. *)
let sref fc (c : string) : string =
  let is_ident x =
    x <> "" && (match x.[0] with '0' .. '9' -> false | _ -> true)
    && String.for_all (fun ch -> ch = '_' || (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9')) x in
  (* the position of the bracket that closes at the end of c, if c ends with one *)
  let opening () =
    let n = String.length c in
    if n = 0 || c.[n - 1] <> ']' then None
    else
      let rec go i depth =
        if i < 0 then None
        else match c.[i] with
          | ']' -> go (i - 1) (depth + 1)
          | '[' -> if depth = 1 then Some i else go (i - 1) (depth - 1)
          | _ -> go (i - 1) depth in
      go (n - 1) 0 in
  let indexed () =
    match opening () with
    | Some i ->
        let base = String.sub c 0 i in
        let pre = "((StnStr*)(" and post = ")->data)" in
        let lp = String.length pre and lq = String.length post and lb = String.length base in
        (* a name, or an element of the data of an array that has a name *)
        is_ident base
        || (lb > lp + lq && String.sub base 0 lp = pre && String.sub base (lb - lq) lq = post
            && is_ident (String.sub base lp (lb - lp - lq)))
    | None -> false in
  let n = String.length c in
  if n > 3 && String.sub c 0 2 = "(*" && c.[n - 1] = ')' && is_ident (String.sub c 2 (n - 3)) then String.sub c 2 (n - 3)
  else if is_ident c || indexed () then "&" ^ c
  else "&" ^ tmp fc TStr c

(* A value for code that is never reached, such as the end of a function whose body always
   fails. 0 is not an initializer for every type, a struct among them, so it is zeroed. *)
let dead_value fc (t : ty) : string =
  let z = fresh fc.st "_z" in
  line fc "%s %s;" (ct fc t) z;
  line fc "memset(&%s, 0, sizeof %s);" z z;
  z

let own fc (x : r) t = if x.owned || not (rc fc t) then x.c else dup_expr fc.st (ts fc t) x.c

let borrow fc (x : r) t =
  if x.owned && rc fc t then begin
    let n = tmp fc t x.c in
    own_in fc n t;
    n
  end else x.c

(* An expression that cannot assign anything: it makes no calls and runs no statements. *)
let rec writes_nothing (e : texpr) =
  match e.e with
  | XLit _ | XVar _ | XFnRef _ | XNone | XLambda _ -> true
  | XField (x, _, _) | XTupleGet (x, _) | XNeg x | XNot x | XConv x -> writes_nothing x
  | XIndex (a, i) -> writes_nothing a && writes_nothing i
  | XSlice (a, lo, hi) -> writes_nothing a && writes_nothing lo && writes_nothing hi
  | XBin (_, a, b) -> writes_nothing a && writes_nothing b
  | XTuple xs | XArray xs | XStruct (_, _, xs) | XVariant (_, _, _, xs) | XFStr xs -> List.for_all writes_nothing xs
  (* a length is read, whatever it is the length of *)
  | XCall (CBuiltin (name, _), args, _) when String.length name > 4 && String.sub name 0 4 = "len@" ->
      List.for_all (fun a -> a.amode = MBorrow && writes_nothing a.a) args
  | _ -> false

(* [first] is a borrowed Str whose use waits for [later], which is about to be generated. Operands
   and arguments are evaluated left to right (section 4.4), and a Str is read by address, so
   [first] is settled now: held with a count of its own, registered before [later] can fail, when
   [later] may assign the variable or element it names; otherwise, when it is an element whose
   index is still to be checked, by its address. A name or a literal is read as it is. *)
let hold_str fc (first : string) (later : texpr) =
  let is_ident x = x <> "" && String.for_all (fun ch -> ch = '_' || (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9')) x in
  let literal = String.length first > 6 && String.sub first 0 6 = "strlit" in
  let named_element =
    (* a name bound, by its address, to an element of an array that does not change *)
    let n = String.length first in
    n > 3 && String.sub first 0 2 = "(*" && first.[n - 1] = ')' && is_ident (String.sub first 2 (n - 3)) in
  if literal then first
  else if not (writes_nothing later) then begin
    let held = tmp fc TStr (dup_expr fc.st TStr first) in
    own_in fc held TStr;
    held
  end
  else if is_ident first || named_element then first
  else if first <> "" && first.[String.length first - 1] = ']' then begin
    let p = fresh fc.st "_p" in
    line fc "StnStr const* %s = &%s;" p first;
    "(*" ^ p ^ ")"
  end
  else tmp fc TStr first

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

(* The entry main calls a looping function through: every function's own name starts fn_, so a
   name that starts stn_entry_ cannot be one. *)
let entry_name cname = "stn_entry_" ^ cname

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
    Buffer.add_string st.helpers (release_fn ("release_" ^ n) ""
      (if needs_rc st t then drop_stmt st t (Printf.sprintf "((%s*)p)->value" n) else ""))
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
      (* the most negative Int has no decimal literal in C: its magnitude does not fit int64_t *)
      if s = "9223372036854775808" || s = "-9223372036854775808" then "INT64_MIN" else Printf.sprintf "INT64_C(%s)" s
  | I32 when s = "-2147483648" -> "INT32_MIN"
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
  | XCall (CBuiltin ("entry@Map", _), _, _) -> Some true
  | XCall (CFn (u, _), _, _) -> (Hashtbl.find fc.st.prog.fns u).fsig.slend
  | XCall (CTrait (tr, ta, m, self, _), _, _) -> (
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

(* Upper bounds for nonnegative machine integers. Unknown values use the
   ordinary checked arithmetic path. Check the proof arithmetic as well. *)
let rec natural_bound fc (e : texpr) =
  match repr (ts fc e.ty) with
  | TInt (IInt | I64) ->
      (match e.e with
       | XLit (LInt value) ->
           let n = Values.parse_int_lit value in
           if n >= 0L then Some n else None
       | XVar v -> Hashtbl.find_opt fc.natural_max v.vid
       | XBin ((Add | Mul | Mod as op), a, b) ->
           (match natural_bound fc a, natural_bound fc b, op with
            | Some a, Some b, Add when a <= Int64.sub Int64.max_int b -> Some (Int64.add a b)
            | Some a, Some b, Mul when b = 0L || a <= Int64.div Int64.max_int b -> Some (Int64.mul a b)
            | Some a, Some _, Mod ->
                (match b.e with
                 | XLit (LInt value) ->
                     let divisor = Values.parse_int_lit value in
                     if divisor > 0L then Some (min a (Int64.pred divisor)) else None
                 | _ -> None)
            | _ -> None)
       | _ -> None)
  | _ -> None

let array_index fc v (index : texpr) value len loc =
  match List.assoc_opt v.vid fc.checked_ranges, natural_bound fc index with
  | Some limit, Some upper when upper <= limit -> value
  | _ -> Printf.sprintf "stn_index(%s, %s, %s)" value len (loc_args loc)

(* The cells for reuse that are left after an if or a match: those that no branch spent. Each
   branch starts with what there was before, so each may use a cell; after them all, a cell that
   any of them used is gone. *)
let unspent before (afters : (string * string * Buffer.t) list list) =
  List.filter (fun (tok, _, _) -> List.for_all (fun after -> List.exists (fun (t', _, _) -> t' = tok) after) afters) before

let note fc (at : Syntax.loc * string) =
  let st = fc.st in
  if !(st.marking) then begin
    st.cur := at;
    st.marks := (fc.b, Buffer.length fc.b, fst at, snd at, List.exists (fun (f : frame) -> f.fk = FLoop) fc.frames) :: !(st.marks)
  end

(* what an expression is, in an error about the code it became *)
let describe (e : texpr) =
  let plain n = match String.index_opt n '@' with Some i -> String.sub n 0 i | None -> n in
  match e.e with
  | XVariant _ -> "this constructor"
  | XStruct _ -> "this struct"
  | XArray _ -> "this array literal"
  | XFStr _ -> "this f-string"
  | XLambda _ -> "this closure"
  | XComp _ -> "this comprehension"
  | XPack _ -> "this conversion to an `any` value"
  | XSlice _ -> "this slice"
  | XCall (CBuiltin (n, _), _, _) -> Printf.sprintf "this call of %s" (plain n)
  | XCall (CTrait (_, _, m, _, _), _, _) -> Printf.sprintf "this call of %s" m
  | XCall (CClosure _, _, _) -> "this call of a function value"
  | XCall (CFn _, _, _) -> "this call"
  | XFail _ -> "this fail"
  | _ -> "this expression"

(* The first call of a function to itself that is neither in tail position nor the one field of a
   constructor in tail position (rule 5 of section 9.6). A return is a tail position wherever it
   stands. *)
let stray_self_call uname (body : texpr) (walk : (texpr -> unit) -> (tstmt -> unit) -> texpr -> unit) =
  let is_self (x : texpr) = match x.e with XCall (CFn (u, _), _, _) -> u = uname | _ -> false in
  let tails = ref [] in
  let rec tail (x : texpr) =
    if is_self x then tails := x :: !tails
    else match x.e with
      | XIf (_, a, b) -> tail a; tail b
      | XMatch (_, arms) -> List.iter (fun a -> tail a.body) arms
      | XBlock (_, v) -> tail v
      | XVariant (_, _, _, fs) ->
          (match List.filter is_self fs with [ one ] -> tails := one :: !tails | _ -> ())
      | _ -> () in
  tail body;
  let all = ref [] in
  walk (fun x -> if is_self x then all := x :: !all)
    (fun s -> match s.st with SReturn x -> tail x | _ -> ()) body;
  List.find_opt (fun x -> not (List.exists (fun y -> y == x) !tails)) (List.rev !all)

let rec expr fc (e : texpr) : r =
  let saved = !(fc.st.cur) in
  note fc (e.l, describe e);
  let r = expr_at fc e in
  note fc saved;
  r

and expr_at fc (e : texpr) : r =
  let st = fc.st in
  let t = ts fc e.ty in
  match List.find_opt (fun (index, _) -> index == e) fc.loop_indices with
  | Some (_, name) -> { c = name; owned = false }
  | None -> match e.e with
  | XLit l -> lit fc t l
  | XNone -> { c = "0"; owned = false }
  | XFStr ps ->
      (* each part is held against the code of the parts after it *)
      let rec parts_of = function
        | [] -> []
        | p :: rest ->
            let c = borrow fc (expr fc p) TStr in
            let c = if rest = [] then c else hold_str fc c { p with e = XFStr rest } in
            c :: parts_of rest in
      let parts = parts_of ps in
      (match parts with
       | [ p ] -> { c = p; owned = false }
       | _ -> { c = tmp fc TStr (Printf.sprintf "stn_str_concat_n(%d, (StnStr[]){ %s })" (List.length parts) (String.concat ", " parts)); owned = true })
  | XVar v ->
      if is_cell fc v then begin
        let p = cell_ptr fc v in
        line fc "if (%s->busy) stn_trap(\"shared cell busy\", %s, \"a shared cell was accessed while it was lent out\");" p (loc_args e.l);
        if rc fc v.vty then { c = tmp fc v.vty (dup_expr st (ts fc v.vty) (var_read fc v)); owned = true }
        else { c = var_read fc v; owned = false }
      end else if moves fc e v then begin
        (* the last occurrence of an owned variable takes its reference with it (section 9.2): a
           consuming use then needs no dup, and a read releases the value when its statement ends.
           The variable is left holding a value that its release at the end of the scope ignores. *)
        let n = var_read fc v in
        let m = tmp fc v.vty n in
        line fc "%s" (moved_out st (ts fc v.vty) n);
        { c = m; owned = true }
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
      { c = Printf.sprintf "%s[%s]" d (array_index fc v i iv n e.l); owned = false }
  | XIndex (a, i) ->
      let av = borrow fc (expr fc a) a.ty in
      let iv = (expr fc i).c in
      let iv = tmp fc (TInt IInt) iv in
      { c = Printf.sprintf "((%s*)(%s)->data)[stn_index(%s, stn_len(%s), %s)]" (ct fc t) av iv av (loc_args e.l); owned = false }
  | XSlice (a, lo, hi) ->
      let av = borrow fc (expr fc a) a.ty in
      (* a string is read by address: it is settled before its bounds, which may assign it *)
      let av = if repr (ts fc a.ty) = TStr then hold_str fc av { lo with e = XTuple [ lo; hi ] } else av in
      let lov = tmp fc (TInt IInt) (expr fc lo).c in
      let hiv = tmp fc (TInt IInt) (expr fc hi).c in
      (match repr (ts fc a.ty) with
       (* a slice of a string that cannot change while it is in scope is a view of it: nothing
          is copied until the slice is stored or returned, when its duplicate is a copy *)
       | TStr when view_source fc a && writes_nothing lo && writes_nothing hi ->
           { c = tmp fc t (Printf.sprintf "stn_str_view(%s, %s, %s, %s)" (sref fc av) lov hiv (loc_args e.l)); owned = false }
       | TStr -> { c = tmp fc t (Printf.sprintf "stn_str_slice(%s, %s, %s, %s)" (sref fc av) lov hiv (loc_args e.l)); owned = true }
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
          let before = !(st.reuse) in
          discard fc a;
          let after_a = !(st.reuse) in
          st.reuse := before;
          fc.ind <- fc.ind - 1;
          line fc "} else {";
          fc.ind <- fc.ind + 1;
          discard fc b;
          st.reuse := unspent before [ after_a; !(st.reuse) ];
          fc.ind <- fc.ind - 1;
          line fc "}";
          { c = "0"; owned = false }
      | _ ->
          let res = fresh st "_r" in
          line fc "%s %s;" (ct fc t) res;
          line fc "if (%s) {" cv;
          fc.ind <- fc.ind + 1;
          let before = !(st.reuse) in
          assign_into fc res a t;
          let after_a = !(st.reuse) in
          st.reuse := before;
          fc.ind <- fc.ind - 1;
          line fc "} else {";
          fc.ind <- fc.ind + 1;
          assign_into fc res b t;
          st.reuse := unspent before [ after_a; !(st.reuse) ];
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
      (* control does not come back, but the checker gave the expression the type it was used at,
         and C wants a value of it *)
      { c = (match repr t with TNever | TUnit -> "0" | _ -> dead_value fc t); owned = false }
  | XComp (body, comps) ->
      let elt = match repr t with TArray et -> et | _ -> assert false in
      let a = fresh st "_t" in
      (* the result grows by doubling; sizing it up front from the source would evaluate
         the source twice *)
      line fc "StnArray* %s = stn_array_new(%s, 4);" a (elem_ops st elt);
      comp_loops fc comps (fun () ->
          let v = own fc (expr fc body) body.ty in
          let n = tmp fc elt v in
          line fc "STN_PUSH(&%s, %s, %s);" a (cty st elt) n);
      { c = a; owned = true }

(* the loops of a comprehension, with [sink] run for each element, in a statement frame of its own *)
and comp_loops fc (comps : tcomp list) (sink : unit -> unit) =
      let rec go = function
        | [] ->
            push fc FStmt;
            sink ();
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
      go comps

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
  let v = if (List.hd fc.frames).owned = [] then v else tmp fc TBool v in
  pop fc;
  v

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
      (* a variant without fields is a tagged word, not a cell: there is no count to raise, so it
         is as good as owned *)
      if vals = [] then { c = Printf.sprintf "((%s)(uintptr_t)((%d << 1) | 1))" (ct fc t) i; owned = true }
      else begin
        let n = fresh st "_b" in
        (* the cell of a value of this type that a match around this took apart is used again
           (section 9.3); it is a counted cell that nothing else held, so its header stands *)
        (* not from inside a loop of the program that the cell was taken apart outside of: the
           loop would find it there once and allocate every other time round *)
        let outside_loop tok =
          let rec go = function
            | [] -> true
            | (f : frame) :: rest -> if List.exists (fun (o, _) -> o = tok) f.owned then true else if f.fk = FLoop then false else go rest in
          go fc.frames in
        (match List.find_opt (fun (tok, m, b) -> m = mangle t && b == fc.b && outside_loop tok) !(st.reuse) with
         | Some (tok, _, _) ->
             (* allocated only when the cell taken apart was shared, and so not a token *)
             let from = Buffer.length fc.b in
             line fc "%s %s = %s ? %s : (%s)stn_alloc(sizeof(struct box_%s));" (ct fc t) n tok tok (ct fc t) (mangle t);
             st.excused := (fc.b, from, Buffer.length fc.b) :: !(st.excused);
             (* the cell is spent: a later constructor on this path allocates, and says so *)
             st.reuse := List.filter (fun (t', _, _) -> t' <> tok) !(st.reuse);
             line fc "%s = NULL;" tok
         | None -> line fc "%s %s = (%s)stn_alloc(sizeof(struct box_%s));" (ct fc t) n (ct fc t) (mangle t));
        line fc "%s->h.tag = %d;" n i;
        List.iteri (fun j x -> line fc "%s->u.%s.f%d = %s;" n (c_ident v.vname_) j x) vals;
        { c = n; owned = true }
      end

(* ---------- calls ---------- *)

(* The arguments of a call, as C expressions. A mut place is evaluated where it is written,
   but its address is taken, and its arrays made unique and its indexes checked, once the
   other arguments have run: they can share an array or change its length, and C leaves open
   in which order the arguments of a call are evaluated. With more than one address, each is
   taken into a variable, in order, so the checks run left to right, as in the interpreter. *)
and arg_strings fc (items : [ `Addr of (unit -> string) * ty | `Arg of string ] list) : string list =
  let many = List.length (List.filter (function `Addr _ -> true | `Arg _ -> false) items) > 1 in
  let rec go = function
    | [] -> []
    | `Arg s :: rest -> s :: go rest
    | `Addr (finish, t) :: rest ->
        let lv = finish () in
        if many then begin
          let p = fresh fc.st "_ap" in
          line fc "%s* %s = &%s;" (ct fc t) p lv;
          p :: go rest
        end else ("&" ^ lv) :: go rest
  in
  go items

and args_c fc (params : (mode * ty) list) (targs : targ list) : string list =
  arg_strings fc
    (List.map2
       (fun (m, pt) ta ->
         match m with
         | MMut ->
             let finish = place_deferred_of_expr fc ta.a in
             hold_busy fc ta.a;
             `Addr (finish, ts fc ta.a.ty)
         | MTake -> `Arg (tmp fc ta.a.ty (own fc (expr fc ta.a) ta.a.ty))
         | MBorrow ->
             let x = expr fc ta.a in
             let v = borrow fc x ta.a.ty in
             `Arg v)
       params targs)

and call fc (e : texpr) (cl : callee) (targs : targ list) convs : r =
  let st = fc.st in
  let t = ts fc e.ty in
  match cl with
  | CFn (uname, tys) ->
      let tys = List.map (ts fc) tys in
      let tf = Hashtbl.find st.prog.fns uname in
      (match tf.fsig.smodule, tf.fsig.sdisplay, tys, targs with
       | "core", ("sort" | "reverse" as name), [ TInt (IInt | I64) ], [ arg ] ->
           let lv = place_lvalue_of_expr fc arg.a in
           line fc "stn_array_%s_i64(&%s);" name lv;
           { c = "0"; owned = false }
       | "core", "contains", [ TInt (IInt | I64) ], [ arr; item ] ->
           let av = borrow fc (expr fc arr.a) arr.a.ty in
           let iv = tmp fc (ts fc item.a.ty) (expr fc item.a).c in
           { c = Printf.sprintf "stn_array_contains_i64(%s, %s)" av iv; owned = false }
       | "core", "or", _, [ sum; fallback ]
         when not (rc fc sum.a.ty) ->
           let sum_ty = ts fc sum.a.ty in
           (match repr sum_ty with
            | TNamed (("Option" | "Result" as name), _) when layout st sum_ty = LInline ->
                let success = if name = "Option" then 1 else 0 in
                let data = List.nth (variants st sum_ty) success |> fst in
                let sv = tmp fc sum_ty (expr fc sum.a).c in
                (* The default is evaluated eagerly, even on a success. *)
                let default = tmp fc t (expr fc fallback.a).c in
                { c = Printf.sprintf "(%s == %d ? %s : %s)"
                          (tag_of st sum_ty sv) success (variant_field st sum_ty data 0 sv) default;
                  owned = false }
            | _ -> call_instance fc e uname tys tf.fsig targs convs)
       | _ -> call_instance fc e uname tys tf.fsig targs convs)
  | CBuiltin (name, tys) -> builtin fc e name (List.map (ts fc) tys) targs convs
  | CTrait (tr, ta, m, self, _) when (match repr (ts fc self) with TAny _ -> true | _ -> false) ->
      any_call fc e tr (List.map (ts fc) ta) m (ts fc self) targs convs
  | CTrait (tr, ta, m, self, own) -> (
      let self = ts fc self and ta = List.map (ts fc) ta in
      match Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) tr ta m self with
      | Some (f, ftys) ->
          let tf = Hashtbl.find st.prog.fns f in
          (* the impl's own type arguments, then the method's *)
          call_instance fc e f (ftys @ List.map (ts fc) own) tf.fsig targs convs
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
    Buffer.add_string st.helpers (release_fn ("anyrel_" ^ crel) ""
      (if needs_rc st at then drop_stmt st at (Printf.sprintf "(*(%s*)((StnAnyBox*)p)->data)" cc) else ""))
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
                         self_struct = None; cached = Hashtbl.create 4; natural_max = Hashtbl.create 4; unique_arrays = []; loop_indices = []; checked_ranges = []; unchecked_pops = []; lend = None } in
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
  (* main is not compiled hot (see emit_fn), and a function that loops, inlined into it, would lose
     that; main calls it through an entry that is hot and never inlined, where it is inlined *)
  let name =
    let is_main = match st.prog.main with Some m -> m = uname | None -> false in
    if !(st.in_main) && sg.slend = None && not is_main && loops st uname then begin
      if not (Hashtbl.mem st.entries name) then Hashtbl.replace st.entries name ("", "");
      entry_name name
    end else name in
  let s = List.combine (List.map fst sg.stparams) tys in
  let ps = List.mapi (fun i (m, _, pt, _) -> ((if Hashtbl.mem st.demoted (uname, i) then MBorrow else m), subst s pt)) sg.sparams in
  if sg.slend <> None then begin
    (* every parameter it can lend from is passed by address, so the place outlives
       the call; the pointer is good for the rest of the caller's statement *)
    let avs =
      arg_strings fc
        (List.map2
           (fun (m, _) ta ->
             match m with
             | MMut -> let finish = place_deferred_of_expr fc ta.a in hold_busy fc ta.a; `Addr (finish, ts fc ta.a.ty)
             | MTake -> `Arg (tmp fc ta.a.ty (own fc (expr fc ta.a) ta.a.ty))
             | MBorrow -> (
                 match to_place fc ta.a with
                 | Some p -> `Addr (place_deferred ~write:false fc p, ts fc ta.a.ty)
                 | None -> `Arg ("&" ^ tmp fc ta.a.ty (borrow fc (expr fc ta.a) ta.a.ty))))
           ps targs)
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
  | TStr -> Printf.sprintf "stn_str_dup(%s)" a
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
  | TNamed (("Map" | "Set"), _) -> Printf.sprintf "((uint8_t)stn_map_eq(%s, %s))" a b
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

(* The hash of a value, as a uint64_t: SipHash of the bytes of a number or a string, an impl of Hash
   of the program where there is one, and otherwise one SipHash over the words of its parts, in
   order: for a tuple, a struct or a data type its fields (a data type's tag first), for an array
   its length and elements. A part that is a string or has an impl of its own adds its hash as a word. *)
and hash_call fc t a : string =
  let st = fc.st in
  match repr t with
  | TStr -> Printf.sprintf "stn_str_hash(%s)" a
  | TInt _ | TBool | TChar | TDur | TBytes -> Printf.sprintf "stn_hash_u64((uint64_t)(%s))" a
  | TFloat | TF32 -> Printf.sprintf "stn_hash_f64((double)(%s))" a
  | TUnit | TNever -> "((uint64_t)0)"
  | _ -> (
      match Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) "Hash" [] "hash" t with
      | Some (f, ftys) -> Printf.sprintf "stn_hash_u64((uint64_t)%s(%s))" (!request_instance st f ftys) a
      | None ->
          let n = "hash_" ^ mangle t in
          if not (Hashtbl.mem st.defined n) then begin
            Hashtbl.replace st.defined n ();
            let c = cty st t in
            pr st.protos "static uint64_t %s(%s x);\n" n c;
            pr st.helpers "static uint64_t %s(%s x) { StnSip s; stn_sip_init(&s); %s return stn_sip_finish(&s); }\n" n c (hash_feed fc t "x")
          end;
          Printf.sprintf "%s(%s)" n a)

(* statements that add the words of a value to the SipHash stream s *)
and hash_feed fc t a : string =
  let st = fc.st in
  match repr t with
  | TInt _ | TBool | TChar | TDur | TBytes -> Printf.sprintf "stn_sip_word(&s, (uint64_t)(%s));" a
  | TFloat | TF32 -> Printf.sprintf "{ double _d = (double)(%s); uint64_t _b; if (_d == 0) _d = 0; memcpy(&_b, &_d, 8); stn_sip_word(&s, _b); }" a
  | TUnit | TNever -> ""
  | TStr -> Printf.sprintf "stn_sip_word(&s, %s);" (hash_call fc t a)
  | _ when Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) "Hash" [] "hash" t <> None ->
      Printf.sprintf "stn_sip_word(&s, %s);" (hash_call fc t a)
  | TArray et ->
      (* names of their own at each level: an element may be an array too *)
      let i = fresh st "_hi" and x = fresh st "_hx" in
      Printf.sprintf "stn_sip_word(&s, (uint64_t)(%s)->len); for (int64_t %s = 0; %s < (%s)->len; %s++) { %s %s = ((%s*)(%s)->data)[%s]; %s }"
        a i i a i (cty st et) x (cty st et) a i (hash_feed fc et x)
  | TTuple ts -> String.concat " " (List.mapi (fun i et -> hash_feed fc et (Printf.sprintf "(%s).f%d" a i)) ts)
  | TNamed _ when is_struct st t -> String.concat " " (List.map (fun (fnm, et) -> hash_feed fc et (Printf.sprintf "(%s).%s" a (fname fnm))) (struct_fields st t))
  | TNamed _ when is_data st t ->
      let arms =
        List.map
          (fun ((v : variant_info), fs) ->
            Printf.sprintf "case %d: { %s break; }" v.vindex
              (String.concat " " (List.mapi (fun i (_, et) -> hash_feed fc et (variant_field st t v i a)) fs)))
          (variants st t)
      in
      Printf.sprintf "stn_sip_word(&s, (uint64_t)%s); switch (%s) { %s }" (tag_of st t a) (tag_of st t a) (String.concat " " arms)
  | _ -> Printf.sprintf "stn_sip_word(&s, %s);" (hash_call fc t a)

(* The table of a Map[K, V] or a Set[K]: how its keys are hashed, compared, counted, and its values. *)
and map_ops fc (t : ty) : string =
  let st = fc.st in
  let k, v = match repr t with TNamed ("Map", [ k; v ]) -> (k, Some v) | TNamed ("Set", [ k ]) -> (k, None) | _ -> failwith "cgen: map_ops" in
  let name = "mapops_" ^ mangle t in
  if not (Hashtbl.mem st.defined name) then begin
    Hashtbl.replace st.defined name ();
    let m = mangle t in
    let kc = cty st k in
    pr st.protos "static uint64_t mhash_%s(const void* p);\nstatic int meq_%s(const void* a, const void* b);\nstatic const StnMapOps %s;\n" m m name;
    pr st.helpers "static uint64_t mhash_%s(const void* p) { return %s; }\n" m (hash_call fc k (Printf.sprintf "(*(const %s*)p)" kc));
    pr st.helpers "static int meq_%s(const void* a, const void* b) { return %s; }\n" m
      (eq_call fc k (Printf.sprintf "(*(const %s*)a)" kc) (Printf.sprintf "(*(const %s*)b)" kc));
    let counted (x : ty) = if needs_rc st x then (ignore (elem_ops st x); let xm = mangle x in ("eldup_" ^ xm, "eldrop_" ^ xm)) else ("NULL", "NULL") in
    let kd, kr = counted k in
    let vsize, vd, vr, veq =
      match v with
      | None -> ("0", "NULL", "NULL", "NULL")
      | Some v ->
          let vc = cty st v in
          let vd, vr = counted v in
          let has_eq = Typecheck.find_impl (Typecheck.rtab_of_prog st.prog) "Eq" [] v <> None in
          let veq =
            if has_eq then begin
              pr st.protos "static int mveq_%s(const void* a, const void* b);\n" m;
              pr st.helpers "static int mveq_%s(const void* a, const void* b) { return %s; }\n" m
                (eq_call fc v (Printf.sprintf "(*(const %s*)a)" vc) (Printf.sprintf "(*(const %s*)b)" vc));
              "mveq_" ^ m
            end else "NULL"
          in
          (Printf.sprintf "sizeof(%s)" vc, vd, vr, veq)
    in
    (* a key of 64 bits that is compared as a number, or a Str with no Eq of the program's, is hashed
       and compared inside the runtime *)
    let kind = match repr k with TInt (IInt | I64 | U64) | TDur | TBytes -> "STN_KEY_I64" | TStr -> "STN_KEY_STR" | _ -> "0" in
    pr st.helpers "static const StnMapOps %s = { sizeof(%s), %s, mhash_%s, meq_%s, %s, %s, %s, %s, %s, %s };\n" name kc vsize m m kd kr vd vr veq kind
  end;
  "&" ^ name

(* a lookup of the key k in the table m, inline when the key is a 64-bit integer *)
and map_find_call (kt : ty) m k =
  match repr kt with
  | TInt (IInt | I64 | U64) | TDur | TBytes -> Printf.sprintf "stn_map_find_i64(%s, (uint64_t)%s)" m k
  | TStr -> Printf.sprintf "stn_map_find_str(%s, %s)" m k
  | _ -> Printf.sprintf "stn_map_find(%s, &%s)" m k

and cmp_call fc t a b : string =
  let st = fc.st in
  match repr t with
  | TStr -> Printf.sprintf "((int64_t)stn_str_cmp(%s, %s))" (sref fc a) (sref fc b)
  | TInt _ | TFloat | TF32 | TBool | TChar | TDur | TBytes -> Printf.sprintf "((int64_t)(((%s) > (%s)) - ((%s) < (%s))))" a b a b
  | _ -> (
      match Typecheck.impl_method_in (Typecheck.rtab_of_prog st.prog) "Ord" [] "cmp" t with
      | Some (f, ftys) -> Printf.sprintf "%s(%s, %s)" (!request_instance st f ftys) a b
      | None -> "0")

and binop fc (e : texpr) op (a : texpr) (b : texpr) : r =
  let st = fc.st in
  let at = ts fc a.ty in
  let xa = expr fc a in
  if op = Add && repr at = TStr && xa.owned then begin
    (* a + b where a is a value of this expression's own, a result or a variable at its last use:
       b is appended to it in place when nothing else holds its buffer (section 9.3). It stays
       registered for release until then, for the paths on which b fails, and is emptied after. *)
    let av = borrow fc xa a.ty in
    let bv = sref fc (borrow fc (expr fc b) b.ty) in
    let res = tmp fc TStr (Printf.sprintf "stn_str_append(%s, %s)" av bv) in
    line fc "%s = (StnStr){ .w0 = 0, .w1 = 0 };" av;
    { c = res; owned = true }
  end else
  let ab = borrow fc xa a.ty in
  let ab = if repr at = TStr then hold_str fc ab b else ab in
  (* Operands are evaluated left to right (section 4.4), but C leaves the order of a
     call's arguments open, and either side may trap. So the left operand stays an
     expression only when it is a variable or a literal and the right one emits no
     statements; otherwise it is saved in a temporary ahead of the right one's code. *)
  let mark = Buffer.length fc.b in
  let bb = borrow fc (expr fc b) b.ty in
  let ab =
    if repr at = TStr then ab
    else if rc fc a.ty || (Buffer.length fc.b = mark && simple_operand ab) then ab
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
        | Lt -> Printf.sprintf "(stn_str_cmp(%s, %s) < 0)" (sref fc ab) (sref fc bb)
        | Le -> Printf.sprintf "(stn_str_cmp(%s, %s) <= 0)" (sref fc ab) (sref fc bb)
        | Gt -> Printf.sprintf "(stn_str_cmp(%s, %s) > 0)" (sref fc ab) (sref fc bb)
        | _ -> Printf.sprintf "(stn_str_cmp(%s, %s) >= 0)" (sref fc ab) (sref fc bb) in
      { c; owned = false }
  | (Eq | Ne), (TUnit | TNever) -> { c = (if op = Eq then "1" else "0"); owned = false }
  | Eq, _ -> plain "=="
  | Ne, _ -> plain "!="
  | Lt, _ -> plain "<"
  | Le, _ -> plain "<="
  | Gt, _ -> plain ">"
  | Ge, _ -> plain ">="
  | Add, TStr -> { c = tmp fc TStr (Printf.sprintf "stn_str_concat(%s, %s)" (sref fc ab) (sref fc bb)); owned = true }
  | Add, TInt (IInt | I64) when natural_bound fc e <> None -> plain "+"
  | Mul, TInt (IInt | I64) when natural_bound fc e <> None -> plain "*"
  | Mod, TInt (IInt | I64) when natural_bound fc e <> None ->
      let uint = match natural_bound fc a, natural_bound fc b with
        | Some a, Some b when max a b <= 0xffff_ffffL -> "uint32_t"
        | _ -> "uint64_t"
      in
      { c = Printf.sprintf "((int64_t)((%s)(%s) %% (%s)(%s)))" uint ab uint bb; owned = false }
  | (Div | Mod), TInt k
    when (match b.e with
          | XLit (LInt lit) -> (let d = Values.parse_int_lit lit in d <> 0L && d <> -1L)
          | _ -> false) ->
      (* a divisor that is a literal other than 0 and -1 can neither be zero nor overflow the
         quotient, so the division is plain C, which the C compiler turns into shifts and multiplies *)
      (* both operands are converted to the type first: a literal such as INT64_C(-9223372036854775808)
         can be unsigned in C, which would make the division unsigned *)
      let ct = cty fc.st (TInt k) in
      { c = Printf.sprintf "((%s)((%s)(%s) %s (%s)(%s)))" ct ct ab (if op = Div then "/" else "%") ct bb; owned = false }
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

(* Destination passing (section 9.5). A call of a function to itself whose result goes straight
   into a field of a constructor that the function then returns is in constructor-tail position.
   The function is generated as a loop: the constructor is built with that field empty and stored
   where the previous turn left a destination, the destination becomes the empty field, and the
   parameters take the call's arguments. Stack use is then constant. [dps_field] says which field
   of a constructor holds such a call, when the call can be turned into a turn of the loop: a
   take parameter takes any argument, and any other parameter must be passed on as it is, unless
   it holds nothing counted. *)
and dps_self fc cname (params : (var * mode * ty) list) (x : texpr) : bool =
  let st = fc.st in
  match x.e with
  | XCall (CFn (u, tys), args, []) when inst_name u (List.map (ts fc) tys) = cname && List.length args = List.length params ->
      List.for_all2 (fun ((v : var), m, t) (a : targ) ->
          match m with
          | MTake -> a.amode = MTake
          | MMut -> false
          | MBorrow -> not (needs_rc st t) || (match a.a.e with XVar w -> w.vid = v.vid | _ -> false))
        params args
  | _ -> false

(* the parameters' next values, from the arguments of a call that becomes a turn of the loop *)
and dps_next fc (params : (var * mode * ty) list) (call : texpr) : (string * string) list =
  let st = fc.st in
  match call.e with
  | XCall (_, args, _) ->
      List.concat
        (List.map2 (fun ((v : var), m, pt) (a : targ) ->
             match m with
             | MTake -> [ (var_name v, tmp fc pt (own fc (expr fc a.a) a.a.ty)) ]
             | MBorrow when not (needs_rc st pt) -> [ (var_name v, tmp fc pt (expr fc a.a).c) ]
             | _ -> [])
           params args)
  | _ -> []

and dps_field fc cname (params : (var * mode * ty) list) (e : texpr) : int option =
  let st = fc.st in
  match e.e with
  | XVariant (_, _, _, es) when is_data st (ts fc e.ty) && layout st (ts fc e.ty) = LBoxed ->
      let self = dps_self fc cname params in
      let hits = List.filteri (fun _ x -> self x) es in
      (match hits with
       | [ call ] ->
           let k = ref (-1) in
           List.iteri (fun j x -> if x == call then k := j) es;
           (* Nothing may run between the call and the constructor, and what follows the call is
              read before it here, where the program reads it after: so it is a literal, or a
              variable the call cannot change. A variable in a shared cell can be changed by a
              closure that the call runs. *)
           let rest_plain = List.for_all (fun (x : texpr) -> match x.e with
               | XLit _ -> true
               | XVar v -> not v.vcell && not v.vcaptured
               | _ -> false)
               (List.filteri (fun j _ -> j > !k) es) in
           if rest_plain then Some !k else None
       | _ -> None)
  | _ -> None

(* whether a body returns a constructor with such a call from a tail position *)
and dps_body fc cname params (e : texpr) : bool =
  let rec tail (e : texpr) =
    match e.e with
    | XBlock (_, v) -> tail v
    | XIf (_, a, b) -> tail a || tail b
    | XMatch (_, arms) -> List.exists (fun (a : tarm) -> tail a.body) arms
    | _ -> dps_field fc cname params e <> None in
  (* what a return statement returns is in tail position too, wherever the statement is *)
  let returned = ref false in
  walk_texpr (fun _ -> ())
    (fun (s : tstmt) -> match s.st with SReturn r -> if tail r then returned := true | _ -> ())
    e;
  tail e || !returned

(* generates e, in tail position of a function that is a loop: every path stores the value at the
   destination and returns, or stores a constructor with an empty field and goes round again *)
and dps_tail fc cname params dst (e : texpr) : unit =
  let st = fc.st in
  let again = dps_tail fc cname params dst in
  note fc (e.l, describe e);
  match e.e with
  | XBlock (ss, v) ->
      line fc "{";
      fc.ind <- fc.ind + 1;
      push fc FScope;
      List.iter (stmt fc) ss;
      again v;
      pop fc;
      fc.ind <- fc.ind - 1;
      line fc "}"
  | XIf (c, a, b) ->
      let cv = cond fc c in
      line fc "if (%s) {" cv;
      fc.ind <- fc.ind + 1;
      let before = !(st.reuse) in
      again a;
      let after_a = !(st.reuse) in
      st.reuse := before;
      fc.ind <- fc.ind - 1;
      line fc "} else {";
      fc.ind <- fc.ind + 1;
      again b;
      st.reuse := unspent before [ after_a; !(st.reuse) ];
      fc.ind <- fc.ind - 1;
      line fc "}"
  | XMatch (s, arms) -> ignore (match_ ~tail:again fc e.ty s arms)
  | XVariant (_, _, i, es) when dps_field fc cname params e <> None ->
      let k = Option.get (dps_field fc cname params e) in
      let t = ts fc e.ty in
      push fc FStmt;
      let next = ref [] in
      let vals =
        List.mapi (fun j (x : texpr) ->
            if j <> k then tmp fc x.ty (own fc (expr fc x) x.ty)
            else begin
              (* the call's arguments, in its place among the fields; the field itself stays empty *)
              next := dps_next fc params x;
              Printf.sprintf "(%s)(uintptr_t)1" (cty st t)
            end) es in
      let cell = construct fc t i vals in
      let vinfo, _ = List.nth (variants st t) i in
      line fc "*%s = %s;" dst cell.c;
      line fc "%s = &%s;" dst (variant_field st t vinfo k cell.c);
      drop_until fc (fun _ -> false);
      List.iter (fun (p, v) -> line fc "%s = %s;" p v) !next;
      (* to the top of the function, whatever loops of the program this is inside *)
      line fc "goto stn_dps_turn;";
      pop fc
  | XCall _ when dps_self fc cname params e ->
      (* a call of the function to itself in tail position is another turn, to the same destination *)
      push fc FStmt;
      let next = dps_next fc params e in
      drop_until fc (fun _ -> false);
      List.iter (fun (p, v) -> line fc "%s = %s;" p v) next;
      (* to the top of the function, whatever loops of the program this is inside *)
      line fc "goto stn_dps_turn;";
      pop fc
  | _ ->
      push fc FStmt;
      let x = expr fc e in
      if repr (ts fc e.ty) <> TNever then begin
        let rv = tmp fc fc.ret (own fc x e.ty) in
        line fc "*%s = %s;" dst rv
      end;
      drop_until fc (fun _ -> false);
      line fc "return _res;";
      pop fc

and match_ ?tail fc t (s : texpr) arms : r =
  let st = fc.st in
  let t = if tail <> None then TUnit else t in
  (* The arms bind borrowed views into the scrutinee, so it must outlive the match even
     when an arm overwrites the place it was read from: hold a reference of our own. *)
  let sx = expr fc s in
  (* whether the match was handed its reference, by a variable at its last use or a result, or
     took one of its own from something borrowed, which still holds the value *)
  let handed = sx.owned in
  (* No reference is needed for a variable this function only borrows and cannot assign: a
     read-only parameter, or what a match on one bound. Whoever lent it holds it for the whole
     call, and nothing here can move it or overwrite it. *)
  let lent = (not sx.owned) && (match s.e with
      | XVar v when not v.vmut && not v.vcell ->
          (match Hashtbl.find_opt fc.vars v.vid with
           | Some (VDirect n) -> not (List.exists (fun (f : frame) -> List.exists (fun (o, _) -> o = n) f.owned) fc.frames)
           | _ -> false)
      | _ -> false) in
  let sv = if lent then tmp fc s.ty sx.c else tmp fc s.ty (own fc sx s.ty) in
  if rc fc s.ty && not lent then own_in fc sv s.ty;
  let has_value = match repr t with TUnit | TNever -> false | _ -> true in
  let res = fresh st "_r" and endl = fresh st "match_end" in
  (* the cells for reuse there were before the match, and what each arm left of them *)
  let outer = !(st.reuse) and arm_afters = ref [] in
  if has_value then line fc "%s %s;" (ct fc t) res;
  List.iter
    (fun arm ->
      let tests, binds = pat_test fc s.ty arm.pat sv in
      let test = if tests = [] then "1" else String.concat " && " tests in
      line fc "if (%s) {" test;
      fc.ind <- fc.ind + 1;
      bind_pattern fc binds;
      (* An arm that takes a boxed value apart into variables consumes it (section 9.3). If
         nothing else holds the value, its fields move into the variables and its cell is kept
         for a constructor of the same type in the arm; otherwise the variables are duplicated
         and the value released. Either way the variables are owned, and the match's own
         reference is spent. *)
      let fields =
        match arm.pat with
        (* only a value the match was handed: one it borrowed is still held by what lent it, so
           its cell could never be used again, and its fields are read where they are *)
        | TPVariant (_, _, i, ps)
          when handed && ps <> [] && is_data st (ts fc s.ty) && layout st (ts fc s.ty) = LBoxed
               && List.for_all (function TPVar _ | TPWild -> true | _ -> false) ps ->
            let vinfo, fs = List.nth (variants st (ts fc s.ty)) i in
            Some (List.mapi (fun j (p, (_, ft)) -> (p, ft, variant_field st (ts fc s.ty) vinfo j sv)) (List.combine ps fs))
        | _ -> None in
      let body () =
        push fc FScope;
        let saved = !(st.reuse) in
        (match fields with
         | Some fs ->
             let sty = ts fc s.ty in
             let tok = fresh st "_tok" in
             line fc "%s %s = NULL;" (cty st sty) tok;
             line fc "if (stn_unique(%s)) {" sv;
             line fc "  %s = %s;" tok sv;
             List.iter (fun (p, ft, path) -> match p with
                 | TPWild when needs_rc st ft -> line fc "  %s" (drop_stmt st ft path)
                 | _ -> ()) fs;
             let from = Buffer.length fc.b in
             line fc "} else {";
             List.iter (fun (p, ft, _) -> match p with
                 | TPVar v when needs_rc st ft -> line fc "  %s" (dup_stmt st ft (var_name v))
                 | _ -> ()) fs;
             line fc "  %s" (drop_stmt st sty sv);
             line fc "}";
             st.excused := (fc.b, from, Buffer.length fc.b) :: !(st.excused);
             line fc "%s = (%s)(void*)1;" sv (cty st sty);
             own_in fc tok (TNamed ("__token", []));
             List.iter (fun (p, ft, _) -> match p with
                 | TPVar v when needs_rc st ft -> own_in fc (var_name v) ft
                 | _ -> ()) fs;
             st.reuse := (tok, mangle sty, fc.b) :: saved
         | None -> ());
        (match tail with
         | Some emit -> emit arm.body   (* which leaves the function, or goes round its loop *)
         | None -> if has_value then assign_into fc res arm.body t else discard fc arm.body);
        pop fc;
        arm_afters := !(st.reuse) :: !arm_afters;
        st.reuse := saved;
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
  st.reuse := unspent outer !arm_afters;
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
  Buffer.add_string st.helpers (release_fn (name ^ "_release") (Printf.sprintf "%s_t* self = (%s_t*)p; (void)self;" name name)
    (String.concat " "
       (List.map
          (fun v ->
            if is_cell fc v then Printf.sprintf "stn_drop(self->%s, release_%s);" (cap_field v) (cell_type st (ts fc v.vty))
            else if rc fc v.vty then drop_stmt st (ts fc v.vty) ("self->" ^ cap_field v)
            else "")
          caps)));
  (* the code *)
  let b = Buffer.create 1024 in
  let params = List.map (fun (v : var) -> (v, (match v.vkind with VParam m -> m | VLocal -> MBorrow))) lam.lparams in
  let header =
    Printf.sprintf "static uint8_t %s_code(StnClosure* self_, %s* _out, StnError* _err%s)" name (cty st ft.fret)
      (String.concat "" (List.map (fun (v, m) -> ", " ^ param_decl st m (ts fc v.vty) (var_name v)) params))
  in
  pr st.protos "%s;\n" header;
  let fc' = { st; b; ind = 1; sub = fc.sub; frames = []; can_fail = true; ret = ft.fret; vars = Hashtbl.create 16; self_struct = Some name; cached = Hashtbl.create 4; natural_max = Hashtbl.create 4; unique_arrays = []; loop_indices = []; checked_ranges = []; unchecked_pops = []; lend = None } in
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
      go (Printf.sprintf "%s[%s]" d (array_index fc p.root ix iv n ix.l)) et rest
  | _ ->
      let start = root () in
      let t0 = match p.via with Some call -> ts fc call.ty | None -> ts fc p.root.vty in
      go start t0 p.path

(* Like place_lvalue, but only the index expressions are evaluated now. Making each array on
   the way unique and checking each index are left to the function returned, which emits them
   when it is called. A call takes the address of a mut place once its other arguments have
   run, and one of them can share an array or change its length. *)
and place_deferred ?(write = true) fc (p : place) : unit -> string =
  let rec go (t : ty) = function
    | [] -> fun lv -> lv
    | PField (_, f) :: rest ->
        let ft = List.assoc f (struct_fields fc.st t) in
        let k = go ft rest in
        fun lv -> k (Printf.sprintf "%s.%s" lv (fname f))
    | PTupleIx i :: rest ->
        let ft = match repr t with TTuple ts_ -> List.nth ts_ i | _ -> assert false in
        let k = go ft rest in
        fun lv -> k (Printf.sprintf "%s.f%d" lv i)
    | PIndex ix :: rest ->
        let et = match repr t with TArray et -> et | _ -> assert false in
        let iv = tmp fc (TInt IInt) (expr fc ix).c in
        let k = go et rest in
        fun lv ->
          if write then line fc "stn_array_make_unique(&%s);" lv;
          k (Printf.sprintf "((%s*)(%s)->data)[stn_index(%s, stn_len(%s), %s)]" (cty fc.st et) lv iv lv (loc_args ix.l))
  in
  match ((if p.via = None then Hashtbl.find_opt fc.cached p.root.vid else None), p.path) with
  | Some (d, n), PIndex ix :: rest ->
      let et = match repr (ts fc p.root.vty) with TArray et -> et | _ -> assert false in
      let iv = tmp fc (TInt IInt) (expr fc ix).c in
      let k = go et rest in
      fun () -> k (Printf.sprintf "%s[%s]" d (array_index fc p.root ix iv n ix.l))
  | _ ->
      let start = place_root fc p in
      let t0 = match p.via with Some call -> ts fc call.ty | None -> ts fc p.root.vty in
      let k = go t0 p.path in
      fun () -> k start

(* where a place starts: its variable, or the place a lend call lends *)
and place_root fc (p : place) : string =
  match p.via with
  | Some call -> (expr fc call).c
  | None ->
  match Hashtbl.find_opt fc.vars p.root.vid with
  | Some (VDirect n) -> n
  | Some (VPtr n) -> "(*" ^ n ^ ")"
  | Some (VCell (n, _)) | Some (VCapCell (n, _)) -> n ^ "->value"
  | Some (VCap n) -> n
  | None -> failwith "cgen: unbound place root"

(* a place expression's address, to be taken later: see place_deferred *)
and place_deferred_of_expr ?(write = true) fc (e : texpr) : unit -> string =
  match to_place fc e with
  | Some p ->
      (match cell_root fc e with
       | Some (c, l) -> line fc "if (%s->busy) stn_trap(\"shared cell busy\", %s, \"a shared cell was accessed while it was lent out\");" c (loc_args l)
       | None -> ());
      place_deferred ~write fc p
  | None ->
      let s = tmp fc e.ty (own fc (expr fc e) e.ty) in
      fun () -> s

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

and loop_over fc (src : titer) (p : tpat) ?(before = fun () -> ()) ?pop_array ?indexed_body (body : unit -> unit) =
  (* [before] runs once the source is evaluated and held, and the loop is about to start: it is
     where the arrays the body uses are hoisted, which must see what the source did to them *)
  let st = fc.st in
  match src with
  | IRange (a, b) ->
      let it = ts fc a.ty in
      let lo = tmp fc it (expr fc a).c and hi = tmp fc it (expr fc b).c in
      let i = fresh st "_i" in
      before ();
      let range_var = match p, natural_bound fc a, natural_bound fc b with
        | TPVar v, Some _, Some upper when upper > 0L && not v.vmut && not v.vcell ->
            Some (v.vid, Int64.pred upper)
        | _ -> None
      in
      let emit_loop ?(advance = "") () =
        if (fc.checked_ranges <> [] && advance = "") || fc.unchecked_pops <> [] then
          line fc "#pragma GCC unroll 2";
        line fc "for (%s %s = %s; %s < %s; %s++%s) {" (ct fc it) i lo i hi i advance;
        fc.ind <- fc.ind + 1;
        push fc FLoop;
        let _, binds = pat_test fc it p i in
        bind_pattern fc binds;
        push fc FScope;
        Option.iter (fun (id, max) -> Hashtbl.replace fc.natural_max id max) range_var;
        body ();
        Option.iter (fun (id, _) -> Hashtbl.remove fc.natural_max id) range_var;
        pop fc;
        pop fc;
        fc.ind <- fc.ind - 1;
        line fc "}"
      in
      let index_guard = match range_var, indexed_body with
        | Some (id, upper), Some code ->
            Hashtbl.replace fc.natural_max id upper;
            let guard = match guarded_indices fc code with [] -> None | guards -> Some guards in
            Hashtbl.remove fc.natural_max id;
            guard
        | _ -> None
      in
      let unique_array = match pop_array, index_guard, indexed_body with
        | None, None, Some code -> local_push_array fc code
        | _ -> None
      in
      let append = match p, indexed_body, repr it with
        | TPVar item, Some code, TInt (IInt | I64) -> affine_array_append fc item code
        | _ -> None
      in
      (* a body that is one unconditional push onto a plain local array: the count is known *)
      (match pop_array, index_guard, append, indexed_body with
       | None, None, None, Some code ->
           let action = match code.e with
             | XBlock ([ { st = SExpr call; _ } ], { e = XLit LUnit; _ }) -> call
             | XBlock ([], call) -> call
             | _ -> code
           in
           (match action.e, single_array_call fc "push@Array" code with
            | XCall (CBuiltin ("push@Array", _), { a = { e = XVar w; _ }; _ } :: _, _), Some v when w.vid = v.vid ->
                let array = var_read fc v in
                line fc "if (%s < %s) stn_array_reserve_hint(&%s, (uint64_t)%s - (uint64_t)%s);" lo hi array hi lo
            | _ -> ())
       | _ -> ());
      (match pop_array, index_guard, unique_array, append with
       | None, None, _, Some (v, base) ->
           let array = var_read fc v in
           let count = fresh st "_count" and done_ = fresh st "_appended" in
           let unique = if List.mem v.vid fc.unique_arrays then "" else Printf.sprintf "stn_unique(%s) && " array in
           line fc "uint8_t %s = 0;" done_;
           line fc "if (%s < %s && %s(uint64_t)%s - (uint64_t)%s <= (uint64_t)STN_MAX_ALLOC) {"
             lo hi unique hi lo;
           fc.ind <- fc.ind + 1;
           let offset = tmp fc it (expr fc base).c in
           let limit = fresh st "_limit" and first = fresh st "_first" in
           line fc "int64_t %s, %s;" first limit;
           line fc "if (!__builtin_add_overflow(%s, %s, &%s) && !__builtin_add_overflow(%s, %s - 1, &%s)) {"
             offset lo first offset hi limit;
           fc.ind <- fc.ind + 1;
           line fc "int64_t %s = (int64_t)((uint64_t)%s - (uint64_t)%s);" count hi lo;
           line fc "if ((uint64_t)%s - (uint64_t)%s > (uint64_t)(%s->cap - %s->len)) stn_array_reserve(&%s, (int64_t)((uint64_t)%s - (uint64_t)%s));" hi lo array array array hi lo;
           let data = fresh st "_data" in
           line fc "int64_t* %s = ((int64_t*)%s->data) + %s->len;" data array array;
           line fc "for (int64_t %s = 0; %s < %s; %s++) %s[%s] = %s + %s;"
             i i count i data i first i;
           line fc "%s->len += %s;" array count;
           line fc "%s = 1;" done_;
           fc.ind <- fc.ind - 1;
           line fc "}";
           fc.ind <- fc.ind - 1;
           line fc "}";
           line fc "if (!%s) {" done_;
           fc.ind <- fc.ind + 1;
           emit_loop ();
           fc.ind <- fc.ind - 1;
           line fc "}"
       | None, None, Some v, _ ->
           line fc "if (stn_unique(%s)) {" (var_read fc v);
           fc.ind <- fc.ind + 1;
           let saved = fc.unique_arrays in
           fc.unique_arrays <- v.vid :: saved;
           emit_loop ();
           fc.unique_arrays <- saved;
           fc.ind <- fc.ind - 1;
           line fc "} else {";
           fc.ind <- fc.ind + 1;
           emit_loop ();
           fc.ind <- fc.ind - 1;
           line fc "}"
       | None, None, None, _ -> emit_loop ()
       | None, Some guards, _, _ ->
           let condition = List.map (fun (_, limit, len, _) ->
               Printf.sprintf "%s > INT64_C(%Ld)" len limit) guards |> String.concat " && " in
           line fc "if (%s) {" condition;
           fc.ind <- fc.ind + 1;
           let saved = fc.checked_ranges and saved_indices = fc.loop_indices in
           fc.checked_ranges <- List.map (fun (id, limit, _, _) -> (id, limit)) guards @ saved;
           let _, _, _, index = List.hd guards in
           let advance =
             match range_var, index.e with
             | Some (id, _),
               XBin (Mod, { e = XBin (Mul, { e = XVar v; _ }, { e = XLit (LInt stride); _ }); _ },
                     { e = XLit (LInt modulus); _ }) when v.vid = id ->
                 (* The range proof bounds the initial product when the loop
                    executes. Adding a reduced stride modulo m needs one
                    subtraction or addition, both of which fit by construction. *)
                 let stride = Values.parse_int_lit stride and modulus = Values.parse_int_lit modulus in
                 let step = Int64.rem stride modulus in
                 let cutoff = Int64.sub modulus step in
                 let residue = fresh st "_index" in
                 line fc "uint64_t %s = ((uint64_t)%s * UINT64_C(%Ld)) %% UINT64_C(%Ld);"
                   residue lo stride modulus;
                 fc.loop_indices <- (index, Printf.sprintf "((int64_t)%s)" residue) :: saved_indices;
                 (* A loop that stores through the index takes the smaller of the two candidates,
                    unsigned: below the cutoff the subtraction wraps to a huge value, so the sum
                    wins. That compiles to a conditional move; a wrap mispredicted while stores
                    are in flight costs far more than the longer chain. A loop that only reads
                    is bound by that chain instead, and keeps the plain selection. *)
                 let stores =
                   match Option.map (fun (b : texpr) -> b.e) indexed_body with
                   | Some (XBlock (stmts, _)) ->
                       List.exists (fun (s : tstmt) ->
                           match s.st with
                           | SAssign ({ path = PIndex _ :: _; _ }, _) -> true
                           | _ -> false) stmts
                   | _ -> false
                 in
                 if stores then
                   Printf.sprintf ", %s = (%s - UINT64_C(%Ld) < %s + UINT64_C(%Ld)) ? %s - UINT64_C(%Ld) : %s + UINT64_C(%Ld)"
                     residue residue cutoff residue step residue cutoff residue step
                 else
                 Printf.sprintf ", %s = %s >= UINT64_C(%Ld) ? %s - UINT64_C(%Ld) : %s + UINT64_C(%Ld)"
                   residue residue cutoff residue cutoff residue step
             | _ -> ""
           in
           emit_loop ~advance ();
           fc.checked_ranges <- saved;
           fc.loop_indices <- saved_indices;
           fc.ind <- fc.ind - 1;
           line fc "} else {";
           fc.ind <- fc.ind + 1;
           emit_loop ();
           fc.ind <- fc.ind - 1;
           line fc "}"
       | Some v, _, _, _ ->
           let array = var_read fc v in
           line fc "if (%s < %s && stn_unique(%s) && (uint64_t)stn_len(%s) >= (uint64_t)%s - (uint64_t)%s) {"
             lo hi array array hi lo;
           fc.ind <- fc.ind + 1;
           (match Option.bind indexed_body (pop_reduction fc v) with
            | Some (sum, loc) ->
                let dst = var_read fc sum in
                line fc "%s = stn_array_sum_popped_i64(%s, (int64_t)((uint64_t)%s - (uint64_t)%s), %s, %s);"
                  dst array hi lo dst (loc_args loc)
            | None ->
                let remaining = fresh st "_remaining" in
                line fc "int64_t %s = stn_len(%s);" remaining array;
                push fc FScope;
                own_in fc (Printf.sprintf "(%s)->len = %s" array remaining) (TNamed ("__array_length", []));
                let saved = fc.unchecked_pops in
                fc.unchecked_pops <- (v.vid, remaining) :: saved;
                emit_loop ();
                fc.unchecked_pops <- saved;
                pop fc);
           fc.ind <- fc.ind - 1;
           line fc "} else {";
           fc.ind <- fc.ind + 1;
           emit_loop ();
           fc.ind <- fc.ind - 1;
           line fc "}")
  | IArray (a, MMut) -> (
      match p with
      | TPVar var ->
          push fc FScope;
          let lv = place_lvalue_of_expr fc a in
          hold_busy fc a;
          let et = match repr (ts fc a.ty) with TArray et -> et | _ -> assert false in
          let i = fresh st "_i" in
          before ();
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
  | IArray ({ e = XCall (CBuiltin (("entries@Map" | "items@Set" as source), tys), [ src ], _); _ }, _) ->
      (* a Map or a Set is walked where it is, entry by entry in insertion order, with no array of
         its entries made first. The loop holds a reference of its own, so a write in the body makes
         the variable a table of its own and the walk goes on over the one it started with. *)
      let tys = List.map (ts fc) tys in
      let mt = ts fc src.a.ty in
      let mv = tmp fc mt (own fc (expr fc src.a) mt) in
      own_in fc mv mt;
      let pos = fresh st "_pos" and e = fresh st "_e" in
      before ();
      line fc "int64_t %s = 0;" pos;
      line fc "for (char* %s; (%s = stn_map_next(%s, &%s)); ) {" e e mv pos;
      fc.ind <- fc.ind + 1;
      push fc FLoop;
      let kt = List.hd tys in
      let et, x =
        if source = "entries@Map" then begin
          let vt = List.nth tys 1 in
          let pair = TTuple [ kt; vt ] in
          (pair, tmp fc pair (Printf.sprintf "(%s){ *(%s*)(%s + %s->koff), *(%s*)(%s + %s->voff) }" (ct fc pair) (ct fc kt) e mv (ct fc vt) e mv))
        end
        else (kt, tmp fc kt (Printf.sprintf "*(%s*)(%s + %s->koff)" (ct fc kt) e mv))
      in
      let _, binds = pat_test fc et p x in
      bind_pattern fc binds;
      push fc FScope;
      body ();
      pop fc;
      pop fc;
      fc.ind <- fc.ind - 1;
      line fc "}"
  | IArray (a, _) ->
      let et = match repr (ts fc a.ty) with TArray et -> et | _ -> assert false in
      (* the loop holds its own reference, so the body may change the variable freely *)
      let av = tmp fc a.ty (own fc (expr fc a) a.ty) in
      own_in fc av a.ty;
      let i = fresh st "_i" in
      let data = fresh st "_data" and len = fresh st "_length" in
      line fc "%s const* %s = (%s const*)%s->data; int64_t %s = stn_len(%s);"
        (ct fc et) data (ct fc et) av len av;
      before ();
      if indexed_body <> None && not (needs_rc st et) then line fc "#pragma GCC unroll 2";
      line fc "for (int64_t %s = 0; %s < %s; %s++) {" i i len i;
      fc.ind <- fc.ind + 1;
      push fc FLoop;
      let x = tmp fc et (Printf.sprintf "%s[%s]" data i) in
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
  let plan = hoist_plan fc body in
  let added = emit_hoists fc plan in
  k ();
  List.iter (Hashtbl.remove fc.cached) added

(* The arrays of [body] that can be hoisted, and whether the body writes each. *)
and hoist_plan fc (body : texpr list) : (var * bool) list =
  let cands = Hashtbl.create 4 in
  let candidate (v : var) =
    match (repr (ts fc v.vty), Hashtbl.find_opt fc.vars v.vid) with
    | TArray _, Some (VDirect _ | VPtr _) when not (Hashtbl.mem fc.cached v.vid) -> Hashtbl.replace cands v.vid v
    | _ -> ()
  in
  List.iter (walk_texpr
      (fun e -> match e.e with XVar v -> candidate v | _ -> ())
      (fun (s : tstmt) -> match s.st with SAssign (p, _) when p.via = None -> candidate p.root | _ -> ())) body;
  List.rev (Hashtbl.fold (fun _ (v : var) acc -> match hoistable v body with Some writes -> (v, writes) :: acc | None -> acc) cands [])

(* Make those arrays unshared (if written) and read their data pointer and length. This is
   done where the loop is about to start: a `for` over a value that shares an array (its own
   array, or a struct that holds it) has made it shared by then, and the write must copy. *)
and emit_hoists fc (plan : (var * bool) list) : int list =
  List.map
    (fun ((v : var), writes) ->
      let lv = var_read fc v in
      let et = match repr (ts fc v.vty) with TArray et -> et | _ -> assert false in
      if writes then line fc "stn_array_make_unique(&%s);" lv;
      let d = fresh fc.st "_d" and n = fresh fc.st "_n" in
      line fc "%s* %s = (%s*)(%s)->data; int64_t %s = stn_len(%s);" (ct fc et) d (ct fc et) lv n lv;
      Hashtbl.replace fc.cached v.vid (d, n);
      v.vid)
    plan

and iter_vars (f : var -> unit) (e : texpr) = walk_texpr (fun (x : texpr) -> match x.e with XVar v -> f v | _ -> ()) (fun _ -> ()) e

(* visit every expression and statement *)
and walk_texpr (fe : texpr -> unit) (fs : tstmt -> unit) (e : texpr) =
  let we = walk_texpr fe fs in
  let wit = function IRange (a, b) -> we a; we b | IArray (a, _) -> we a in
  let rec ws (s : tstmt) =
    fs s;
    match s.st with
    | SLet (_, e) | SVar (_, e) | SExpr e | SReturn e | SAssert (e, _) | SAssertFails (_, e) | SCheck e -> we e
    | SAssign (p, e) ->
        Option.iter we p.via;
        List.iter (function PIndex i -> we i | _ -> ()) p.path;
        we e
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

(* Whether a function loops, itself or through a function it calls by name. *)
and loops st uname =
  match Hashtbl.find_opt st.loops uname with
  | Some b -> b
  | None ->
      Hashtbl.replace st.loops uname false;   (* a cycle of calls adds nothing *)
      let found = ref false in
      (match Hashtbl.find_opt st.prog.fns uname with
       | Some tf ->
           walk_texpr
             (fun (x : texpr) -> match x.e with
                | XComp _ -> found := true
                | XCall (CFn (u, _), _, _) -> if not !found && loops st u then found := true
                | _ -> ())
             (fun (s : tstmt) -> match s.st with SWhile _ | SFor _ -> found := true | _ -> ())
             tf.fbody
       | None -> ());
      Hashtbl.replace st.loops uname !found;
      !found

(* Check length once for up to two arrays with bounded subscripts. The
   fallback retains the per-access trap and its original source location. *)
and guarded_indices fc body =
  let guards = ref [] and count = ref 0 in
  let inspect v (index : texpr) =
    match index.e, Hashtbl.find_opt fc.cached v.vid, natural_bound fc index with
    | (XBin (Mod, _, _) | XVar _), Some (_, len), Some limit ->
        (match List.find_opt (fun (id, _, _, _) -> id = v.vid) !guards with
         | None when !count < 2 ->
             incr count;
             guards := (v.vid, limit, len, index) :: !guards
         | Some (_, prior, _, _) when limit > prior ->
             guards := List.map (fun ((id, _, _, _) as old) ->
                 if id = v.vid then (id, limit, len, index) else old) !guards
         | _ -> ())
    | _ -> ()
  in
  walk_texpr
    (fun e -> match e.e with XIndex ({ e = XVar v; _ }, index) -> inspect v index | _ -> ())
    (fun (s : tstmt) -> match s.st with
       | SAssign ({ via = None; root; path = PIndex index :: _; _ }, _) -> inspect root index
       | _ -> ())
    body;
  List.rev !guards

(* Push and clear preserve uniqueness on a direct local array of Copy
   scalars. Indexed reads return scalars and cannot create aliases. *)
and local_push_array fc body =
  let candidate = ref None in
  let allowed = ref [] in
  let permit receiver = allowed := receiver :: !allowed in
  walk_texpr (fun e -> match e.e with
    | XCall (CBuiltin (("push@Array" | "clear@Array"), _),
             { a = ({ e = XVar v; _ } as receiver); _ } :: _, _)
      when not v.vcell && not v.vcaptured && v.vkind = VLocal
           && not (List.mem v.vid fc.unique_arrays)
           && (match Hashtbl.find_opt fc.vars v.vid with Some (VDirect _) -> true | _ -> false)
           && (match repr (ts fc v.vty) with TArray (TInt _ | TBool | TFloat | TF32 | TChar) -> true | _ -> false) ->
        permit receiver;
        if !candidate = None then candidate := Some v
    | XIndex (({ e = XVar _; _ } as receiver), _) -> permit receiver
    | _ -> ()) (fun _ -> ()) body;
  match !candidate with
  | None -> None
  | Some v ->
      let safe = ref true in
      walk_texpr (fun e -> match e.e with
        | XVar w when w.vid = v.vid && not (List.exists ((==) e) !allowed) -> safe := false
        | _ -> ())
        (fun (s : tstmt) -> match s.st with
          | SAssign (p, _) when p.root.vid = v.vid -> safe := false
          | _ -> ()) body;
      if !safe then Some v else None

(* A pure sum of popped integers can run entirely over a tight descending
   range, preserving each checked addition and the final array length. *)
and pop_reduction fc array body =
  match repr (ts fc array.vty), body.e with
  | TArray (TInt (IInt | I64)),
    XBlock ([ { st = SAssign (place,
               ({ e = XBin (Add, { e = XVar lhs; _ },
                 { e = XCall (CFn (callee, _),
                     [ { a = { e = XCall (CBuiltin ("pop@Array", _),
                               [ { a = { e = XVar receiver; _ }; _ } ], _); _ }; _ } ], _); _ }); _ } as add)); _ } ],
             { e = XLit LUnit; _ })
    when place.via = None && place.path = [] && lhs.vid = place.root.vid && not lhs.vcell
         && receiver.vid = array.vid
         && (match repr (ts fc lhs.vty) with TInt (IInt | I64) -> true | _ -> false) ->
      let signature = (Hashtbl.find fc.st.prog.fns callee).fsig in
      if signature.smodule = "core" && signature.sdisplay = "unwrap" then Some (lhs, add.l) else None
  | _ -> None

(* Only one syntactic push or pop, on a direct local array, can execute per iteration.
   Reject other uses, nested iteration, and closures so neither the identity nor
   the reference count can change on the specialized path. *)
and single_array_call fc builtin body =
  let candidate = ref None and allowed = ref true in
  walk_texpr (fun e ->
    match e.e with
    | XCall (CBuiltin (name, _), { a = ({ e = XVar v; _ } as receiver); _ } :: _, _)
      when name = builtin && not v.vcell && not v.vcaptured && v.vkind = VLocal
           && (match Hashtbl.find_opt fc.vars v.vid with Some (VDirect _) -> true | _ -> false) ->
        (match !candidate with None -> candidate := Some (v, receiver) | Some _ -> allowed := false)
    | XLambda _ | XComp _ -> allowed := false
    | _ -> ())
    (fun (s : tstmt) -> match s.st with SFor _ | SWhile _ | SLocalFn _ -> allowed := false | _ -> ())
    body;
  match !candidate with
  | Some (v, receiver) when !allowed ->
      walk_texpr (fun e -> match e.e with
          | XVar w when w.vid = v.vid && e != receiver -> allowed := false
          | _ -> ())
        (fun (s : tstmt) -> match s.st with
          | SAssign (p, _) when p.root.vid = v.vid -> allowed := false
          | _ -> ()) body;
      if !allowed then Some v else None
  | _ -> None

(* With a single push of an affine Int value, the range endpoints prove every
   addition fits. The fast path uses existing capacity and commits length once. *)
and affine_array_append fc item body =
  let action = match body.e with
    | XBlock ([ { st = SExpr call; _ } ], { e = XLit LUnit; _ }) -> call
    | XBlock ([], call) -> call
    | _ -> body
  in
  let rec invariant e =
    match e.e with
    | XLit (LInt _) -> true
    | XVar v ->
        v.vid <> item.vid && not v.vcell
        && (match Hashtbl.find_opt fc.vars v.vid with Some (VDirect _) -> true | _ -> false)
    | XBin ((Add | Sub | Mul), a, b) -> invariant a && invariant b
    | _ -> false
  in
  let affine = match action.e with
    | XCall (CBuiltin ("push@Array", _), [ _; { a = { e = XBin (Add, base, { e = XVar index; _ }); _ }; _ } ], _)
      when index.vid = item.vid && invariant base -> Some base
    | XCall (CBuiltin ("push@Array", _), [ _; { a = { e = XBin (Add, { e = XVar index; _ }, base); _ }; _ } ], _)
      when index.vid = item.vid && invariant base -> Some base
    | _ -> None
  in
  match affine with
  | Some base ->
      (match single_array_call fc "push@Array" body with
       | Some v when (match repr (ts fc v.vty) with TArray (TInt (IInt | I64)) -> true | _ -> false) ->
           Some (v, base)
       | _ -> None)
  | _ -> None

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
          if p.root.vid = v.vid then
            (match p.via, p.path with None, PIndex _ :: _ -> writes := true | _ -> good := false);
          Option.iter visit_child p.via;
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

and declare_var ?(owned = true) fc (v : var) (init : string) =
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
    if owned && needs_rc st t then own_in fc n t
  end

(* The immutable array continues to hold these strings for the entire
   binding's lifetime. Reading the element does not need a second owner. *)
and stable_string_source fc (e : texpr) =
  let immutable v =
    match Hashtbl.find_opt fc.vars v.vid with
    (* VPtr: a let that names an element of an array that does not change *)
    | Some (VDirect _ | VPtr _) -> not v.vmut && v.vkind <> VParam MMut
    | _ -> false
  in
  match e.e with
  | XLit (LStr _) -> true
  | XVar v | XIndex ({ e = XVar v; _ }, _) -> immutable v
  | _ -> false

(* Whether this occurrence of v moves it: it is the last one (note_moves), nothing borrows from v
   to the end of its scope, and v is a plain local that owns a value of a type whose release
   ignores what moved_out leaves behind. *)
and moves fc (e : texpr) (v : var) =
  List.memq e !(fc.st.movable)
  && not (Hashtbl.mem fc.st.pinned v.vid)
  && not v.vcell
  && (match Hashtbl.find_opt fc.vars v.vid with
      | Some (VDirect n) -> List.exists (fun (f : frame) -> List.exists (fun (o, _) -> o = n) f.owned) fc.frames
      | _ -> false)
  && (match repr (ts fc v.vty) with
      | TStr | TArray _ | TNamed (("Map" | "Set"), _) -> true
      | TNamed _ as t -> is_data fc.st t && layout fc.st t = LBoxed
      | _ -> false)

(* what a moved variable is left holding: an empty string, or a pointer that stn_drop ignores *)
and moved_out st t n =
  match repr t with
  | TStr -> Printf.sprintf "%s = (StnStr){ .w0 = 0, .w1 = 0 };" n
  | _ -> Printf.sprintf "%s = (%s)(void*)1;" n (cty st t)

(* Finds the occurrences that may move a variable (section 9.2). An occurrence qualifies when it
   is the last of its variable in the order of evaluation, the only one in its statement (an
   earlier one in the same statement may still be borrowed when this one is reached), and not in
   a loop or closure that the variable was declared outside of. Occurrences in other branches of
   an if or a match do not count against it: they are on paths this one is not on, so the last
   occurrence in each branch moves. Variables that a slice, an alias,
   a match or a loop borrows from are pinned: they keep their value to the end of their scope. *)
and note_moves st (owned_params : var list) (body : texpr) =
  let next = ref 0 in
  let fresh () = incr next; !next in
  let occs : (int, (texpr option * int * int * (int * int) list) list) Hashtbl.t = Hashtbl.create 32 in
  (* the branches the code being walked is inside: each an if or a match, and which arm of it *)
  let path : (int * int) list ref = ref [] in
  let in_arm id arm f = let saved = !path in path := (id, arm) :: saved; f (); path := saved in
  let apart p q = List.exists (fun (id, a) -> List.exists (fun (id', a') -> id = id' && a <> a') q) p in
  let decl : (int, int) Hashtbl.t = Hashtbl.create 32 in
  (* statements that assign a whole variable, `x = e`, with no break or continue inside e *)
  let kills : (int * int, int) Hashtbl.t = Hashtbl.create 16 in
  let jumps = ref 0 in
  let use (v : var) node stmt ctx =
    Hashtbl.replace occs v.vid ((node, stmt, ctx, !path) :: (try Hashtbl.find occs v.vid with Not_found -> [])) in
  let rec root (e : texpr) =
    match e.e with
    | XVar v -> Some v
    | XField (b, _, _) | XTupleGet (b, _) | XIndex (b, _) | XSlice (b, _, _) -> root b
    | _ -> None in
  let pin e = match root e with Some v -> Hashtbl.replace st.pinned v.vid () | None -> () in
  let rec we stmt ctx (e : texpr) =
    let w = we stmt ctx in
    match e.e with
    | XVar v -> use v (Some e) stmt ctx
    | XLit _ | XNone | XFnRef _ -> ()
    | XFStr es | XTuple es | XArray es | XStruct (_, _, es) | XVariant (_, _, _, es) -> List.iter w es
    | XCall (cl, args, _) -> (match cl with CClosure f -> w f | _ -> ()); List.iter (fun a -> w a.a) args
    | XField (b, _, _) | XTupleGet (b, _) | XNeg b | XNot b | XTry b | XConv b | XFail b | XPack b -> w b
    | XIndex (a, b) | XBin (_, a, b) -> w a; w b
    | XSlice (a, b, c) -> pin a; w a; w b; w c
    | XIf (a, b, c) -> w a; let id = fresh () in in_arm id 0 (fun () -> w b); in_arm id 1 (fun () -> w c)
    | XBlock (ss, v) -> List.iter (ws ctx) ss; we (fresh ()) ctx v
    | XMatch (s, arms) ->
        (* the match holds a reference of its own, so its arms borrow from that, not from s;
           the variables an arm takes a value apart into may be owned (see match_) *)
        w s;
        let rec bound = function
          | TPVar v -> Hashtbl.replace decl v.vid ctx
          | TPVariant (_, _, _, ps) | TPStruct (_, _, ps) | TPTuple ps -> List.iter bound ps
          | TPErrType (_, p) -> bound p
          | TPWild | TPLit _ -> () in
        let id = fresh () in
        (* a guard runs on the way to the arms after it too *)
        List.iteri (fun i a -> bound a.pat; Option.iter w a.guard; in_arm id i (fun () -> w a.body)) arms
    | XLambda lam -> we stmt (fresh ()) lam.lbody
    | XComp (b, cs) ->
        let inner = fresh () in
        List.iter (fun cp ->
            (match cp.csrc with IRange (a, b) -> we stmt inner a; we stmt inner b | IArray (a, _) -> pin a; we stmt inner a);
            Option.iter (we stmt inner) cp.ccond) cs;
        we stmt inner b
  and ws ctx (s : tstmt) =
    let stmt = fresh () in
    let w = we stmt ctx in
    match s.st with
    | SLet (p, e) ->
        (* a let can only borrow from a binding that cannot change *)
        (match root e with Some r when not r.vmut -> pin e | _ -> ());
        w e;
        (match p with TPVar v -> Hashtbl.replace decl v.vid ctx | _ -> ())
    | SVar (v, e) ->
        (* only a variable kept as a view borrows from what it starts as *)
        if Hashtbl.mem st.self_sliced v.vid then pin e;
        w e;
        Hashtbl.replace decl v.vid ctx
    | SExpr e | SReturn e | SAssert (e, _) | SAssertFails (_, e) | SCheck e -> w e
    | SLend e -> pin e; w e
    | SAssign (p, e) ->
        Option.iter w p.via;
        List.iter (function PIndex i -> w i | _ -> ()) p.path;
        let before = !jumps in
        w e;
        (* a write into the variable uses it; a write of the whole variable does not *)
        if p.path <> [] || p.via <> None then use p.root None stmt ctx
        else if !jumps = before then Hashtbl.replace kills (p.root.vid, stmt) ctx
    | SBreak | SContinue -> incr jumps
    | SWhile (c, b) -> let inner = fresh () in we stmt inner c; we stmt inner b
    | SFor (_, it, b) ->
        (match it with IRange (a, b) -> w a; w b | IArray (a, _) -> pin a; w a);
        we stmt (fresh ()) b
    | SLocalFn (_, lam) -> we stmt (fresh ()) lam.lbody
  in
  List.iter (fun (v : var) -> Hashtbl.replace decl v.vid 0) owned_params;
  we (fresh ()) 0 body;
  Hashtbl.iter (fun vid ctx ->
      let all = try Hashtbl.find occs vid with Not_found -> [] in
      (* latest first: an occurrence moves when every later one, and every other one of its
         statement, is in another branch *)
      let rec go later = function
        | [] -> ()
        | ((node, stmt, c, p) as o) :: earlier ->
            (match node with
             | Some node when c = ctx
                              && List.for_all (fun (_, _, _, q) -> apart p q) later
                              && List.for_all (fun (_, s, _, q) -> s <> stmt || apart p q) earlier ->
                 st.movable := node :: !(st.movable)
             | _ -> ());
            go (o :: later) earlier in
      go [] all) decl;
  (* `x = f(take x)`: the one occurrence of x in a statement that then assigns x. Nothing can read
     x between the two, so it moves wherever the statement is, in a loop too, and whatever follows. *)
  Hashtbl.iter (fun (vid, stmt) ctx ->
      match List.filter (fun (_, s, _, _) -> s = stmt) (try Hashtbl.find occs vid with Not_found -> []) with
      | [ (Some node, _, c, _) ] when c = ctx && not (List.memq node !(st.movable)) -> st.movable := node :: !(st.movable)
      | _ -> ()) kills

(* The variables of a body whose every assignment is a slice of themselves, `v = v[a..b]` with
   bounds that write nothing, and which are never passed as mut: candidates to be kept as views. *)
and note_self_sliced st (body : texpr) =
  let sliced = Hashtbl.create 8 and spoiled = Hashtbl.create 8 in
  walk_texpr
    (fun (x : texpr) -> match x.e with
       | XCall (_, args, _) ->
           List.iter (fun a -> if a.amode = MMut then iter_vars (fun v -> Hashtbl.replace spoiled v.vid ()) a.a) args
       | _ -> ())
    (fun (s : tstmt) -> match s.st with
       | SAssign ({ via = None; path = []; root; _ }, { e = XSlice ({ e = XVar src; _ }, lo, hi); _ })
         when src.vid = root.vid && writes_nothing lo && writes_nothing hi -> Hashtbl.replace sliced root.vid ()
       | SAssign (p, _) -> Hashtbl.replace spoiled p.root.vid ()
       | SFor (_, IArray (a, MMut), _) -> iter_vars (fun v -> Hashtbl.replace spoiled v.vid ()) a
       | _ -> ())
    body;
  Hashtbl.iter (fun vid () -> if not (Hashtbl.mem spoiled vid) then Hashtbl.replace st.self_sliced vid ()) sliced

(* A string that a view may point into: a binding that cannot change and lives to the end of its
   scope, or a variable that is itself kept as a view of one. *)
and view_source fc (e : texpr) =
  stable_string_source fc e
  || (match e.e with
      | XVar v -> Hashtbl.mem fc.st.view_vars v.vid
      | _ -> false)

(* A let or var of a slice of such a string keeps the view. *)
and binds_view fc (v : var) (e : texpr) =
  match repr (ts fc e.ty), e.e with
  (* bounds that may assign make the slice a copy of a held string, not a view (see XSlice) *)
  | TStr, XSlice (a, lo, hi) when not v.vcell -> view_source fc a && writes_nothing lo && writes_nothing hi
  | _ -> false

(* A let that only names a binding that cannot change, or a field or element of one, borrows it
   (section 9.1): the binding it names is pinned, so it keeps the value alive to the end of a
   scope that encloses this one, and the let neither counts nor releases it. A use that consumes
   the let duplicates it then, as for any borrowed variable. *)
and borrows_stable fc (v : var) (e : texpr) =
  let immutable (w : var) =
    match Hashtbl.find_opt fc.vars w.vid with
    | Some (VDirect _ | VPtr _) -> not w.vmut && w.vkind <> VParam MMut && not w.vcell
    | _ -> false in
  let rec stable (x : texpr) =
    match x.e with
    | XVar w -> immutable w
    | XField (b, _, _) | XTupleGet (b, _) -> stable b
    | XIndex (a, i) -> stable a && writes_nothing i
    | _ -> false in
  not v.vcell && not v.vcaptured && rc fc e.ty && stable e

and borrows_array_string fc (v : var) (e : texpr) =
  match repr (ts fc e.ty), e.e with
  | TStr, XIndex _ when not v.vmut && not v.vcell -> stable_string_source fc e
  | _ -> false

(* A pure Boolean count is monotone. Its per-element additions can be
   replaced by one checked add, with the original overflow location. *)
and array_reduction fc p src body =
  let target lhs place =
    place.via = None && place.path = [] && lhs.vid = place.root.vid && not lhs.vcell
    && (match repr (ts fc lhs.vty) with TInt (IInt | I64) -> true | _ -> false)
  in
  match p, src, body.e with
  | TPVar bit, IArray (array, MBorrow),
    XBlock ([ { st = SExpr { e = XIf ({ e = XVar tested; _ }, yes, { e = XLit LUnit; _ }); _ }; _ } ],
             { e = XLit LUnit; _ }) when bit.vid = tested.vid ->
      (match repr (ts fc array.ty), yes.e with
       | TArray TBool,
         XBlock ([ { st = SAssign (place, ({ e = XBin (Add, { e = XVar lhs; _ }, { e = XLit (LInt "1"); _ }); _ } as add)); _ } ],
                  { e = XLit LUnit; _ })
         when target lhs place -> Some (`Count, lhs, array, add.l)
       | _ -> None)
  | TPVar item, IArray (array, MBorrow),
    XBlock ([ { st = SAssign (place,
               ({ e = XBin (Add, { e = XVar lhs; _ }, { e = XVar element; _ }); _ } as add)); _ } ],
             { e = XLit LUnit; _ })
    when item.vid = element.vid && target lhs place
         && (match repr (ts fc array.ty) with TArray (TInt (IInt | I64)) -> true | _ -> false) ->
      Some (`Sum, lhs, array, add.l)
  | _ -> None

and stmt fc (s : tstmt) =
  let st = fc.st in
  note fc (s.sl, "this statement");
  push fc FStmt;
  (match s.st with
   | SLet (TPVar v, e) when borrows_array_string fc v e ->
       let c = (expr fc e).c in
       let f = List.hd fc.frames in
       fc.frames <- List.tl fc.frames;
       emit_drops fc f;
       (* the element of an array that does not change is named where it is, not copied: a Str is
          read by address, and a copy would be stored to the stack only to be read back *)
       (match sref fc c with
        | addr when addr = "&" ^ c ->
            let n = var_name v in
            line fc "StnStr const* %s = %s;" n addr;
            Hashtbl.replace fc.vars v.vid (VPtr n)
        | _ -> declare_var ~owned:false fc v (tmp fc e.ty c));
       fc.frames <- { fk = FStmt; owned = [] } :: fc.frames
   | SLet (TPVar v, e) when borrows_stable fc v e && not (borrows_array_string fc v e) ->
       let x = expr fc e in
       let init = tmp fc e.ty (if x.owned then x.c else x.c) in
       let f = List.hd fc.frames in
       fc.frames <- List.tl fc.frames;
       emit_drops fc f;
       declare_var ~owned:x.owned fc v init;
       fc.frames <- { fk = FStmt; owned = [] } :: fc.frames
   | SLet (TPVar v, e) when binds_view fc v e ->
       (* the view is the variable: it is not counted, and it cannot outlive what it views *)
       let c = (expr fc e).c in
       let f = List.hd fc.frames in
       fc.frames <- List.tl fc.frames;
       emit_drops fc f;
       declare_var ~owned:false fc v c;
       fc.frames <- { fk = FStmt; owned = [] } :: fc.frames
   | SVar (v, e) when Hashtbl.mem st.self_sliced v.vid && not v.vcell && repr (ts fc v.vty) = TStr ->
       (* a variable whose only assignments are slices of itself (`rest = rest[k..]`) is kept as a
          view, which each of them moves along. It views a string that outlives it: the binding it
          starts from when that cannot change, otherwise a value held here, beside it, to the end
          of its scope. *)
       let x = expr fc e in
       let borrowed = (not x.owned) && (view_source fc e || binds_view fc v e || (match e.e with XLit _ -> true | _ -> false)) in
       let f = List.hd fc.frames in
       fc.frames <- List.tl fc.frames;
       let from =
         if borrowed then tmp fc e.ty x.c
         else begin
           let held = tmp fc e.ty (own fc x e.ty) in
           own_in fc held e.ty;   (* in the enclosing scope, where the variable is *)
           held
         end in
       emit_drops fc f;
       declare_var ~owned:false fc v (Printf.sprintf "stn_str_as_view(%s)" from);
       Hashtbl.replace st.view_vars v.vid ();
       fc.frames <- { fk = FStmt; owned = [] } :: fc.frames
   | SLet (TPVar v, e) | SVar (v, e) ->
       let x = expr fc e in
       (* evaluate fully before the statement's temporaries are released *)
       let x = if not x.owned && rc fc e.ty then { x with c = tmp fc e.ty x.c } else x in
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
       (* a value with nothing counted in it has no drop function to call *)
       if rc fc e.ty then own_in fc n e.ty;
       let _, binds = pat_test fc e.ty p n in
       bind_pattern fc binds;
       fc.frames <- { fk = FStmt; owned = [] } :: fc.frames
   | SAssign ({ via = None; path = []; root; _ },
              ({ e = XBin (Add, { e = XVar lhs; _ }, rhs); ty = TInt (IInt | I64); _ } as e))
     when lhs.vid = root.vid && not root.vcell
          && (match Hashtbl.find_opt fc.vars root.vid with Some (VDirect _) -> true | _ -> false)
          && natural_bound fc e = None
          && (let rec quiet (x : texpr) =
                match x.e with
                | XLit _ | XVar _ -> true
                | XBin ((Add | Sub | Mul), a, b) -> quiet a && quiet b
                | XField (b, _, _) | XTupleGet (b, _) -> quiet b
                | XIndex (a, i) -> quiet a && quiet i
                | _ -> false
              in
              quiet rhs) ->
       (* `v = v + e` on a plain local, where e writes nothing: the checked add stores straight
          into v, which compiles to an add and a jump on overflow. e is evaluated first, and it
          cannot change v, so the value and the trap are the ones the general form gives. *)
       let x = expr fc rhs in
       let rv = tmp fc (TInt IInt) (borrow fc x rhs.ty) in
       let dst = var_read fc root in
       line fc "if (__builtin_add_overflow(%s, %s, &%s)) stn_overflow(%s);" dst rv dst (loc_args e.l)
   | SAssign ({ via = None; path = []; root; _ }, { e = XSlice ({ e = XVar src; _ }, lo, hi); l; _ })
     when src.vid = root.vid && not root.vcell && repr (ts fc root.vty) = TStr
          && (match Hashtbl.find_opt fc.vars root.vid with Some (VDirect _) -> true | _ -> false)
          && writes_nothing lo && writes_nothing hi ->
       (* `v = v[a..b]`: a view moves, a buffer of v's own is cut down in place *)
       let lov = tmp fc (TInt IInt) (expr fc lo).c in
       let hiv = tmp fc (TInt IInt) (expr fc hi).c in
       line fc "stn_str_slice_self(&%s, %s, %s, %s);" (var_read fc root) lov hiv (loc_args l)
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
   | SReturn e when (match !(st.dps) with Some (_, b, _) -> b == fc.b | None -> false) ->
       (* in a function that runs as a loop (section 9.5), what is returned is in tail position *)
       (match !(st.dps) with Some (_, _, tail) -> tail e | None -> ())
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
   | SFor (p, src, body) ->
       (match array_reduction fc p src body with
        | Some (`Count, lhs, array, loc) ->
            let av = borrow fc (expr fc array) array.ty in
            let count = tmp fc (TInt IInt) (Printf.sprintf "stn_array_count_true(%s)" av) in
            let dst = var_read fc lhs in
            line fc "%s = stn_add_i64(%s, %s, %s);" dst dst count (loc_args loc)
        | Some (`Sum, lhs, array, loc) ->
            let av = tmp fc array.ty (borrow fc (expr fc array) array.ty) in
            let dst = var_read fc lhs in
            line fc "%s = stn_array_sum_i64(%s, %s, %s);" dst av dst (loc_args loc)
        | None ->
            let plan = hoist_plan fc [ body ] in
            let added = ref [] in
            let pop_array = match src with IRange _ -> single_array_call fc "pop@Array" body | _ -> None in
            loop_over fc src p ~before:(fun () -> added := emit_hoists fc plan) ?pop_array ~indexed_body:body
              (fun () -> discard fc body);
            List.iter (Hashtbl.remove fc.cached) !added)
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
  (* the first two arguments as Str, the first held against the code of the second *)
  let b2 () =
    let x = hold_str fc (b 0) (arg 1).a in
    (x, b 1) in
  let o i = tmp fc (arg i).a.ty (own fc (expr fc (arg i).a) (arg i).a.ty) in
  let m i = place_lvalue_of_expr fc (arg i).a in
  (* a receiver whose address is taken after the other arguments have run, as for any mut place *)
  let md i = place_deferred_of_expr fc (arg i).a in
  let unit_ () = { c = "0"; owned = false } in
  let value c = { c; owned = false } in
  let owned c = { c = tmp fc t c; owned = true } in
  let elt () = match tys with [ x ] -> x | _ -> TUnit in
  match name with
  | "print@Str" -> line fc "stn_print(%s);" (sref fc (b 0)); unit_ ()
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
  | "read_all@" -> owned (Printf.sprintf "stn_read_all(%s)" (loc_args e.l))
  | "clock_ns@" -> value "stn_clock_ns()"
  | "bench_more@Str" ->
      (* the strings are literals and the numbers plain, so evaluating them each turn of the
         measured loop counts as nothing *)
      let name = sref fc (b 0) and label = sref fc (b 1) in
      let n = b 2 in
      let spec = sref fc (b 3) in
      value (Printf.sprintf "stn_bench_more(%s, %s, %s, %s, %s, %s, %s, %s)" name label n spec (b 4) (b 5) (b 6) (b 7))
  | "len@Array" -> (
      match (arg 0).a.e with
      | XVar v when Hashtbl.mem fc.cached v.vid -> value (snd (Hashtbl.find fc.cached v.vid))
      | _ -> value (Printf.sprintf "stn_len(%s)" (b 0)))
  | "len@Str" -> value (Printf.sprintf "stn_str_len(%s)" (b 0))
  | "push@Array" ->
      let fin = md 0 in
      let x = o 1 in
      let lv = fin () in
      (match (arg 0).a.e with
       | XVar v when List.mem v.vid fc.unique_arrays ->
           line fc "STN_PUSH_UNIQUE(&%s, %s, %s);" lv (cty st (elt ())) x
       | _ -> line fc "STN_PUSH(&%s, %s, %s);" lv (cty st (elt ())) x);
      unit_ ()
  | "pop@Array" ->
      let lv = m 0 in
      let x = fresh st "_x" in
      line fc "%s %s;" (cty st (elt ())) x;
      let ok = fresh st "_ok" in
      (match (arg 0).a.e with
       | XVar v when List.mem_assoc v.vid fc.unchecked_pops ->
           line fc "uint8_t %s = 1; %s = ((%s*)(%s)->data)[--%s];"
             ok x (cty st (elt ())) lv (List.assoc v.vid fc.unchecked_pops)
       | _ -> line fc "uint8_t %s; STN_POP(&%s, %s, %s, %s);" ok lv (cty st (elt ())) x ok);
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
      let fin = md 0 in
      let i = tmp fc (TInt IInt) (expr fc (arg 1).a).c in
      let x = o 2 in
      let lv = fin () in
      line fc "stn_array_insert(&%s, %s, &%s, %s);" lv i x la;
      unit_ ()
  | "remove@Array" ->
      let fin = md 0 in
      let i = tmp fc (TInt IInt) (expr fc (arg 1).a).c in
      let lv = fin () in
      let x = fresh st "_x" in
      line fc "%s %s;" (cty st t) x;
      line fc "stn_array_remove(&%s, %s, &%s, %s);" lv i x la;
      { c = x; owned = true }
  | "clear@Array" ->
      let slot = fresh st "_slot" in
      line fc "StnArray** %s = &%s;" slot (m 0);
      (match (arg 0).a.e with
       | XVar v when List.mem v.vid fc.unique_arrays -> line fc "(*%s)->len = 0;" slot
       | _ when not (needs_rc st (elt ())) ->
           line fc "if (stn_unique(*%s)) (*%s)->len = 0; else stn_array_clear(%s);" slot slot slot
       | _ -> line fc "stn_array_clear(%s);" slot);
      unit_ ()
  | "extend@Array" ->
      let fin = md 0 in
      let ys = b 1 in
      let lv = fin () in
      line fc "stn_array_extend(&%s, %s);" lv ys;
      unit_ ()
  | "filled@Int" ->
      let n = tmp fc (TInt IInt) (expr fc (arg 0).a).c in
      let x = b 1 in
      let xt = tmp fc (elt ()) x in
      (match repr (elt ()) with
       | TInt (IInt | I64) -> owned (Printf.sprintf "stn_array_filled_i64(%s, %s, %s, %s)" (elem_ops st (elt ())) n xt la)
       | _ -> owned (Printf.sprintf "stn_array_filled(%s, %s, &%s, %s)" (elem_ops st (elt ())) n xt la))
  | "repeat@Array" ->
      (* [x; n]: the element is evaluated first and owned while the count runs, which may
         replace the variable it was read from; the scope drops it once the copies are made *)
      let xt = o 0 in
      if rc fc (elt ()) then own_in fc xt (elt ());
      let n = tmp fc (TInt IInt) (expr fc (arg 1).a).c in
      (match repr (elt ()) with
       | TInt (IInt | I64) -> owned (Printf.sprintf "stn_array_filled_i64(%s, %s, %s, %s)" (elem_ops st (elt ())) n xt la)
       | _ -> owned (Printf.sprintf "stn_array_filled(%s, %s, &%s, %s)" (elem_ops st (elt ())) n xt la))
  (* ---- maps and sets (section 3.6) ---- *)
  | "lit@Map" | "lit@Set" ->
      let is_map = name = "lit@Map" in
      let mt = TNamed ((if is_map then "Map" else "Set"), tys) in
      let step = if is_map then 2 else 1 in
      let n = List.length targs / step in
      let m = tmp fc mt (Printf.sprintf "stn_map_with_capacity(%s, %d)" (map_ops fc mt) n) in
      own_in fc m mt;
      for i = 0 to n - 1 do
        let k = o (i * step) in
        if is_map then begin
          let v = o (i * step + 1) in
          line fc "stn_map_put(&%s, &%s, &%s);" m k v
        end else line fc "stn_map_put(&%s, &%s, NULL);" m k
      done;
      { c = dup_expr st mt m; owned = true }
  | ("from_pairs@Map" | "from_items@Set")
    when (match (arg 0).a.e with XComp (body, _) -> (name = "from_items@Set" || (match body.e with XTuple [ _; _ ] -> true | _ -> false)) | _ -> false) ->
      (* a comprehension into a Map or a Set puts each element as it is made, with no array first *)
      let is_map = name = "from_pairs@Map" in
      let mt = TNamed ((if is_map then "Map" else "Set"), tys) in
      let body, comps = match (arg 0).a.e with XComp (b, cs) -> (b, cs) | _ -> assert false in
      let m = fresh st "_t" in
      line fc "StnMap* %s = stn_map_new(%s);" m (map_ops fc mt);
      comp_loops fc comps (fun () ->
          match body.e with
          | XTuple [ ke; ve ] when is_map ->
              let k = tmp fc ke.ty (own fc (expr fc ke) ke.ty) in
              let v = tmp fc ve.ty (own fc (expr fc ve) ve.ty) in
              line fc "stn_map_put(&%s, &%s, &%s);" m k v
          | _ ->
              let k = tmp fc body.ty (own fc (expr fc body) body.ty) in
              line fc "stn_map_put(&%s, &%s, NULL);" m k);
      { c = m; owned = true }
  | "from_pairs@Map" | "from_items@Set" ->
      (* the array of the comprehension is owned here: its elements move into the table, and it is
         freed without dropping them *)
      let is_map = name = "from_pairs@Map" in
      let mt = TNamed ((if is_map then "Map" else "Set"), tys) in
      let et = if is_map then TTuple tys else List.hd tys in
      let a = o 0 in
      let m = tmp fc mt (Printf.sprintf "stn_map_with_capacity(%s, %s->len)" (map_ops fc mt) a) in
      let i = fresh st "_i" in
      line fc "for (int64_t %s = 0; %s < %s->len; %s++) {" i i a i;
      line fc "  %s _x = ((%s*)%s->data)[%s];" (cty st et) (cty st et) a i;
      if is_map then line fc "  stn_map_put(&%s, &_x.f0, &_x.f1);" m else line fc "  stn_map_put(&%s, &_x, NULL);" m;
      line fc "}";
      line fc "if (stn_unique(%s)) stn_free(%s); else { for (int64_t %s = 0; %s < %s->len; %s++) { %s } stn_drop(%s, stn_array_release); }" a a i i a i
        (if needs_rc st et then dup_stmt st et (Printf.sprintf "((%s*)%s->data)[%s]" (cty st et) a i) else "") a;
      { c = m; owned = true }
  | "entries@Map" ->
      let kt, vt = (List.nth tys 0, List.nth tys 1) in
      let pair = TTuple [ kt; vt ] in
      let m = tmp fc (TNamed ("Map", tys)) (b 0) in
      let a = tmp fc (TArray pair) (Printf.sprintf "stn_array_new(%s, (%s)->len > 0 ? (%s)->len : 1)" (elem_ops st pair) m m) in
      let pos = fresh st "_pos" and e = fresh st "_e" in
      line fc "{ int64_t %s = 0; for (char* %s; (%s = stn_map_next(%s, &%s)); ) {" pos e e m pos;
      line fc "  %s _k = *(%s*)(%s + (%s)->koff); %s _v = *(%s*)(%s + (%s)->voff);" (cty st kt) (cty st kt) e m (cty st vt) (cty st vt) e m;
      line fc "  ((%s*)%s->data)[%s->len++] = (%s){ %s, %s };" (cty st pair) a a (cty st pair) (dup_expr st kt "_k") (dup_expr st vt "_v");
      line fc "} }";
      { c = a; owned = true }
  | "items@Set" ->
      let kt = List.hd tys in
      let m = tmp fc (TNamed ("Set", tys)) (b 0) in
      let a = tmp fc (TArray kt) (Printf.sprintf "stn_array_new(%s, (%s)->len > 0 ? (%s)->len : 1)" (elem_ops st kt) m m) in
      let pos = fresh st "_pos" and e = fresh st "_e" in
      line fc "{ int64_t %s = 0; for (char* %s; (%s = stn_map_next(%s, &%s)); ) {" pos e e m pos;
      line fc "  %s _k = *(%s*)(%s + (%s)->koff);" (cty st kt) (cty st kt) e m;
      line fc "  ((%s*)%s->data)[%s->len++] = %s;" (cty st kt) a a (dup_expr st kt "_k");
      line fc "} }";
      { c = a; owned = true }
  | "len@Map" | "len@Set" -> value (Printf.sprintf "((%s)->len)" (b 0))
  | "index@Map" | "index_or@Map" | "get@Map" ->
      let kt, vt = (List.nth tys 0, List.nth tys 1) in
      let m = tmp fc (TNamed ("Map", tys)) (b 0) in
      let k = tmp fc kt (b 1) in
      let start = if name = "index_or@Map" then Some (o 2) else None in
      let p = fresh st "_p" in
      line fc "%s* %s = (%s*)%s;" (cty st vt) p (cty st vt) (map_find_call (List.hd tys) m k);
      (match name, start with
       | "index@Map", _ ->
           line fc "if (!%s) stn_trap(\"missing key\", %s, \"the Map has no entry for this key\");" p la;
           { c = tmp fc vt (dup_expr st vt ("*" ^ p)); owned = true }
       | "index_or@Map", Some start ->
           let res = fresh st "_r" in
           line fc "%s %s;" (cty st vt) res;
           line fc "if (%s) { %s = %s; %s } else %s = %s;" p res (dup_expr st vt ("*" ^ p))
             (if needs_rc st vt then drop_stmt st vt start else "") res start;
           { c = res; owned = true }
       | _ ->
           let res = fresh st "_r" in
           line fc "%s %s;" (ct fc t) res;
           line fc "if (%s) {" p;
           let held = tmp fc vt (dup_expr st vt ("*" ^ p)) in
           let sv = construct fc t 1 [ held ] in
           line fc "  %s = %s;" res sv.c;
           line fc "} else {";
           let nv = construct fc t 0 [] in
           line fc "  %s = %s;" res nv.c;
           line fc "}";
           { c = res; owned = true })
  | "contains@Map" | "contains@Set" ->
      let mt = TNamed ((if name = "contains@Map" then "Map" else "Set"), tys) in
      let m = tmp fc mt (b 0) in
      let k = tmp fc (List.hd tys) (b 1) in
      value (tmp fc TBool (Printf.sprintf "(%s != NULL)" (map_find_call (List.hd tys) m k)))
  | "put@Map"
    when (match (arg 0).a.e, (arg 1).a.e, (arg 2).a.e with
          | XVar root, XVar key, XBin ((Add | Sub | Mul | Div | Mod), { e = XCall (CBuiltin ("index_or@Map", _), [ { a = { e = XVar root'; _ }; _ }; { a = { e = XVar key'; _ }; _ }; _ ], _); _ }, rhs) ->
              (* m[k] op= e where e is a literal or another variable: nothing in it can reach the Map *)
              root.vid = root'.vid && key.vid = key'.vid
              && (match rhs.e with XLit _ -> true | XVar w -> w.vid <> root.vid && not w.vcell | _ -> false)
          | _ -> false) ->
      (* the entry is found once, or made with the default of its type, and updated where it is *)
      let vt = ts fc (List.nth tys 1) in
      let op, start, rhs =
        match (arg 2).a.e with
        | XBin (op, { e = XCall (_, [ _; _; start ], _); _ }, rhs) -> (op, start.a, rhs)
        | _ -> assert false
      in
      let fin = md 0 in
      (* the key is borrowed: it is counted again only if a new entry keeps it *)
      let k = tmp fc (ts fc (List.hd tys)) (b 1) in
      let lv = fin () in
      let fresh_ = fresh st "_fresh" and p = fresh st "_p" in
      (match repr (ts fc (List.hd tys)) with
       | TInt (IInt | I64 | U64) | TDur | TBytes | TStr ->
           (* a key of 64 bits or a Str that is there already is found inline, in a table nothing else holds *)
           line fc "int %s = 0; %s* %s = stn_unique(%s) ? (%s*)%s : NULL;" fresh_ (ct fc vt) p lv (ct fc vt) (map_find_call (ts fc (List.hd tys)) lv k);
           line fc "if (__builtin_expect(!%s, 0)) %s = (%s*)stn_map_slot_ref(&%s, &%s, &%s);" p p (ct fc vt) lv k fresh_
       | _ -> line fc "int %s; %s* %s = (%s*)stn_map_slot_ref(&%s, &%s, &%s);" fresh_ (ct fc vt) p (ct fc vt) lv k fresh_);
      line fc "if (%s) {" fresh_;
      fc.ind <- fc.ind + 1;
      let sv = expr fc start in
      line fc "*%s = %s;" p (own fc sv start.ty);
      fc.ind <- fc.ind - 1;
      line fc "}";
      (* the value in the entry stands in for a variable of the operation *)
      let cur = new_var "$entry" vt false VLocal in
      Hashtbl.replace fc.vars cur.vid (VDirect (Printf.sprintf "(*%s)" p));
      let next = expr fc { e = XBin (op, { e = XVar cur; ty = vt; l = e.l }, rhs); ty = vt; l = (arg 2).a.l } in
      let nv = tmp fc vt (own fc next vt) in
      Hashtbl.remove fc.vars cur.vid;
      if needs_rc st vt then line fc "%s" (drop_stmt st vt (Printf.sprintf "(*%s)" p));
      line fc "*%s = %s;" p nv;
      unit_ ()
  | "put@Map" ->
      let fin = md 0 in
      let kt = ts fc (List.hd tys) and vt = ts fc (List.nth tys 1) in
      let k = o 1 in
      let v = o 2 in
      let lv = fin () in
      (match repr kt with
       | TInt (IInt | I64 | U64) | TDur | TBytes | TStr ->
           (* an entry that is there already, in a table nothing else holds, is found inline and its
              value replaced in place; the key given is let go, as stn_map_put would *)
           let p = fresh st "_p" in
           line fc "%s* %s = stn_unique(%s) ? (%s*)%s : NULL;" (ct fc vt) p lv (ct fc vt) (map_find_call kt lv k);
           line fc "if (%s) { %s %s *%s = %s; } else stn_map_put(&%s, &%s, &%s);" p
             (if needs_rc st kt then drop_stmt st kt k else "")
             (if needs_rc st vt then drop_stmt st vt ("*" ^ p) else "") p v lv k v
       | _ -> line fc "stn_map_put(&%s, &%s, &%s);" lv k v);
      unit_ ()
  | "entry@Map" ->
      (* the place of the value of a key that is there, in a table made unshared first; a key that
         is missing traps, as m[k] does *)
      let kt = ts fc (List.hd tys) and vt = ts fc (List.nth tys 1) in
      let fin = md 0 in
      let k = tmp fc kt (b 1) in
      let lv = fin () in
      let p = fresh st "_entry" in
      line fc "stn_map_make_unique_for_write(&%s);" lv;
      line fc "%s* %s = (%s*)%s;" (ct fc vt) p (ct fc vt) (map_find_call kt lv k);
      line fc "if (!%s) stn_trap(\"missing key\", %s, \"the Map has no entry for this key\");" p la;
      value (Printf.sprintf "(*%s)" p)
  | "add@Set" ->
      let fin = md 0 in
      let k = o 1 in
      let lv = fin () in
      line fc "stn_map_put(&%s, &%s, NULL);" lv k;
      unit_ ()
  | "remove@Map" ->
      let vt = List.nth tys 1 in
      let fin = md 0 in
      let k = tmp fc (List.hd tys) (b 1) in
      let lv = fin () in
      let out = fresh st "_x" and res = fresh st "_r" in
      line fc "%s %s; %s %s;" (cty st vt) out (ct fc t) res;
      line fc "if (stn_map_remove(&%s, &%s, &%s)) {" lv k out;
      let sv = construct fc t 1 [ out ] in
      line fc "  %s = %s;" res sv.c;
      line fc "} else {";
      let nv = construct fc t 0 [] in
      line fc "  %s = %s;" res nv.c;
      line fc "}";
      { c = res; owned = true }
  | "remove@Set" ->
      let fin = md 0 in
      let k = tmp fc (List.hd tys) (b 1) in
      let lv = fin () in
      value (tmp fc TBool (Printf.sprintf "((uint8_t)stn_map_remove(&%s, &%s, NULL))" lv k))
  | "clear@Map" | "clear@Set" ->
      let lv = m 0 in
      line fc "stn_map_clear(&%s);" lv;
      unit_ ()
  | "union@Set" | "intersection@Set" | "difference@Set" ->
      let st_ = TNamed ("Set", tys) in
      ignore (map_ops fc st_);
      let a = tmp fc st_ (b 0) in
      let bb = tmp fc st_ (b 1) in
      let f = match name with "union@Set" -> "stn_set_union" | "intersection@Set" -> "stn_set_intersection" | _ -> "stn_set_difference" in
      owned (Printf.sprintf "%s(%s, %s)" f a bb)
  | "copy@T" ->
      let x = expr fc (arg 0).a in
      { c = tmp fc t (own fc x t); owned = true }
  | "unreachable@Str" ->
      line fc "stn_trap_str(\"unreachable\", %s, %s);" la (b 0);
      let res = fresh st "_r" in
      line fc "%s %s;" (ct fc t) res;
      line fc "memset(&%s, 0, sizeof %s);" res res;
      { c = res; owned = false }
  | "byte_at_or_end@Str" ->
      let s = hold_str fc (b 0) (arg 1).a in
      let i = tmp fc (TInt IInt) (b 1) in
      value (Printf.sprintf "stn_str_byte_at_or_end(%s, %s)" (sref fc s) i)
  | "chars@Str" -> owned (Printf.sprintf "stn_str_chars(%s, %s)" (sref fc (b 0)) (elem_ops st TChar))
  | "split@Str" -> let s, sep = b2 () in let s = sref fc s and sep = sref fc sep in owned (Printf.sprintf "stn_str_split(%s, %s, %s, %s)" s sep (elem_ops st TStr) la)
  | "join@Array" -> (
      match (arg 0).a.e with
      | XArray parts ->
          let parts = List.map (fun part ->
              let value = expr fc part in
              if not value.owned && stable_string_source fc part then tmp fc TStr value.c
              else begin
                let x = tmp fc TStr (own fc value TStr) in
                own_in fc x TStr;
                x
              end) parts in
          let sep = b 1 in
          let args = if parts = [] then "NULL" else "(StnStr[]){ " ^ String.concat ", " parts ^ " }" in
          owned (Printf.sprintf "stn_str_join_parts(%s, %d, %s)" args (List.length parts) sep)
      | _ ->
          let xs = b 0 in
          let sep = b 1 in
          owned (Printf.sprintf "stn_str_join(%s, %s)" xs sep))
  | "trim@Str" -> owned (Printf.sprintf "stn_str_trim(%s)" (sref fc (b 0)))
  | "find_or_end@Str" ->
      (* both strings are held against the code of what follows them *)
      let s = hold_str fc (b 0) { (arg 1).a with e = XTuple [ (arg 1).a; (arg 2).a ] } in
      let x = hold_str fc (b 1) (arg 2).a in
      let from = tmp fc (TInt IInt) (b 2) in
      value (Printf.sprintf "stn_str_find(%s, %s, %s)" (sref fc s) (sref fc x) from)
  | "contains@Str" -> let s, x = b2 () in let s = sref fc s and x = sref fc x in value (Printf.sprintf "stn_str_contains(%s, %s)" s x)
  | ("starts_with@Str" | "ends_with@Str") ->
      let prefix = name = "starts_with@Str" in
      (match (arg 1).a.e with
       | XLit (LStr literal) ->
           let s = sref fc (b 0) in
           let n = String.length literal in
           let offset = if prefix then "" else Printf.sprintf " + (stn_str_len(*%s) - %d)" s n in
           let data = Printf.sprintf "(stn_str_ptr(%s)%s)" s offset in
           let cmp at width =
             let bytes = c_string (String.sub literal at width) in
             if width = 2 || width = 4 || width = 8 then
               let bits = width * 8 in
               Printf.sprintf "(stn_load_u%d(%s + %d) == stn_load_u%d(%s))" bits data at bits bytes
             else Printf.sprintf "(memcmp(%s + %d, %s, %d) == 0)" data at bytes width
           in
           (* Two fixed-width, overlapping comparisons avoid a libc call
              for short literals between the native comparison widths. *)
           let same =
             if n <= 1 || n > 16 then cmp 0 n
             else
               let width = if n < 4 then 2 else if n < 8 then 4 else 8 in
               if n = width then cmp 0 width
               else Printf.sprintf "(%s & %s)" (cmp 0 width) (cmp (n - width) width)
           in
           if n >= 1 && n <= 8 then begin
             (* a literal of up to eight bytes is compared as one word: the first or last eight
                bytes of the string, read from its words when it is inline *)
             let w = ref 0L in
             for i = n - 1 downto 0 do w := Int64.logor (Int64.shift_left !w 8) (Int64.of_int (Char.code literal.[i])) done;
             if prefix then
               let mask = if n = 8 then "UINT64_MAX" else Printf.sprintf "UINT64_C(0x%Lx)" (Int64.sub (Int64.shift_left 1L (8 * n)) 1L) in
               value (Printf.sprintf "stn_str_starts8(%s, %d, %s, UINT64_C(0x%Lx))" s n mask !w)
             else value (Printf.sprintf "stn_str_ends8(%s, %d, UINT64_C(0x%Lx))" s n !w)
           end else
           value (Printf.sprintf "(stn_str_len(*%s) >= %d && %s)" s n same)
       | _ ->
           let s, p = b2 () in
           let s = sref fc s and p = sref fc p in
           value (Printf.sprintf "stn_str_%s(%s, %s)" (if prefix then "starts_with" else "ends_with") s p))
  | "repeat@Str" ->
      (* the string is settled before the count is evaluated, which may assign it *)
      let held = hold_str fc (b 0) (arg 1).a in
      let n = tmp fc (TInt IInt) (expr fc (arg 1).a).c in
      let s = sref fc held in owned (Printf.sprintf "stn_str_repeat(%s, %s, %s)" s n la)
  | "parse_int@Str" | "parse_float@Str" ->
      let s = sref fc (b 0) in
      let is_int = name = "parse_int@Str" in
      let out = fresh st "_v" in
      line fc "%s %s;" (if is_int then "int64_t" else "double") out;
      let rcv = tmp fc (TInt IInt) (Printf.sprintf "%s(%s, &%s)" (if is_int then "stn_parse_int" else "stn_parse_float") s out) in
      let pe = TNamed ("ParseError", []) in
      ignore (err_id st pe);
      line fc "if (%s) {" rcv;
      fc.ind <- fc.ind + 1;
      let sd = tmp fc TStr (dup_expr st TStr ("(*" ^ s ^ ")")) in
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
  let params = List.mapi (fun i ((v : var), (m, _, t, _)) -> (v, (if Hashtbl.mem st.demoted (uname, i) then MBorrow else m), subst sub t))
      (List.combine tf.fparams sg.sparams) in
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
  let fc = { st; b; ind = 1; sub; frames = []; can_fail; ret; vars = Hashtbl.create 32; self_struct = None; cached = Hashtbl.create 4; natural_max = Hashtbl.create 4; unique_arrays = []; loop_indices = []; checked_ranges = []; unchecked_pops = []; lend = sg.slend } in
  (* A C compiler guesses how often each block runs, and treats the late arms of a long chain of
     tests as cold: a loop inlined there is then compiled for size, without the conditional moves
     it would get anywhere else. Every Starnite function is compiled for speed instead. *)
  (* main is left out: it runs once, and made hot it has the whole program inlined into it, where
     the C compiler loses what the restrict parameters of the functions it inlines said (the
     spectral-norm benchmark ran 2.1 times as long) *)
  let is_main = match st.prog.main with Some m -> m = uname | None -> false in
  st.marking := sg.smods <> [] || st.explain || st.profile;
  st.marks := []; st.excused := [];
  st.cur := (sg.sloc, "this function");
  (* what verify.ml reads of a noalloc or inplace function, once its code is written *)
  let record () =
    if sg.smods <> [] || st.explain then begin
      let mine l = List.filter_map (fun (b', a, x, y, z) -> if b' == b then Some (a, x, y, z) else None) l in
      (* a function with type parameters is checked in each form the program uses, and named so *)
      let display = if tys = [] then sg.sdisplay else Printf.sprintf "%s[%s]" sg.sdisplay (String.concat ", " (List.map show_ty tys)) in
      st.records := { Verify.cname; display; mods = sg.smods; floc = sg.sloc; text = Buffer.contents b;
                      marks = List.rev (mine !(st.marks));
                      excused = List.filter_map (fun (b', lo, hi) -> if b' == b then Some (lo, hi) else None) !(st.excused);
                      stray = Option.map (fun (x : texpr) -> x.l) (stray_self_call uname tf.fbody walk_texpr) } :: !(st.records)
    end;
    st.names := (cname, sg.sdisplay) :: !(st.names);
    st.marking := false in
  note_self_sliced st tf.fbody;
  st.movable := [];
  note_moves st (List.filter_map (fun (v, m, _) -> if m = MTake then Some v else None) params) tf.fbody;
  pr b "%s%s {\n" (if is_main then "" else "STN_HOT ") header;
  (* the entry main calls this through, if it loops: the same parameters, hot, never inlined *)
  if not (is_main || lend) then begin
    let entry = entry_name cname in
    let names = List.map (fun (v, _, _) -> var_name v) params in
    let args = String.concat ", " ((if can_fail then [ "_out"; "_err" ] else []) @ names) in
    let eheader =
      if can_fail then Printf.sprintf "static uint8_t %s(%s* _out, StnError* _err%s)" entry (cty st ret) (String.concat "" (List.map (fun p -> ", " ^ p) plist))
      else Printf.sprintf "static %s %s(%s)" (cty st ret) entry (if plist = [] then "void" else String.concat ", " plist) in
    Hashtbl.replace st.entry_defs cname
      (Printf.sprintf "STN_NOINLINE %s;\n" eheader,
       Printf.sprintf "STN_HOT STN_NOINLINE %s { return %s(%s); }\n" eheader cname args)
  end;
  st.in_main := is_main;
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
    record ();
    Buffer.add_buffer st.funcs b
  end else if (not can_fail) && List.for_all (fun ((v : var), m, _) -> m <> MMut && not v.vcell) params
            && dps_body fc cname params tf.fbody then begin
    (* a function that returns a constructor holding a call of itself runs as a loop (section 9.5) *)
    line fc "%s _res;" (cty st ret);
    line fc "%s* _dst = &_res;" (cty st ret);
    st.dps := Some ("_dst", fc.b, dps_tail fc cname params "_dst");
    (* a turn is a jump to this label, not a continue: a call that becomes a turn may be inside a
       loop of the program, whose next turn a continue would start *)
    line fc "stn_dps_turn: {";
    fc.ind <- fc.ind + 1;
    dps_tail fc cname params "_dst" tf.fbody;
    fc.ind <- fc.ind - 1;
    line fc "}";
    line fc "stn_trap(\"unreachable\", __FILE__, __LINE__, 0, \"a function ended without a value\");";
    st.dps := None;
    fc.frames <- [];
    pr b "}\n\n";
    st.in_main := false;
    record ();
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
  st.in_main := false;
  record ();
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
          let fc = { st; b = Buffer.create 64; ind = 0; sub = []; frames = []; can_fail = false; ret = TStr; vars = Hashtbl.create 1; self_struct = None; cached = Hashtbl.create 4; natural_max = Hashtbl.create 4; unique_arrays = []; loop_indices = []; checked_ranges = []; unchecked_pops = []; lend = None } in
          pr b "    case %d: return %s;\n" id (show_call fc t (err_val st t "e")))
        pending;
      loop ()
    end
  in
  loop ();
  pr b "    default: return stn_str_new(\"error\", 5);\n  }\n}\n";
  b

(* Demoting take to borrow (section 9.4). A take parameter that its function only reads is passed
   as a read-only one: the caller keeps its reference, and no count is updated for the call. It
   applies to a private function called only by name: not exported, not main, not a method of an
   impl, not used as a value, since each of those has callers that go by the signature as written.
   A parameter is only read when every occurrence of it, and of the variables a match on it binds,
   is a field or element read, an operand, the subject of a match or of a for, or an argument to a
   read-only parameter or to a take parameter that is itself demoted. Whatever stores it, returns
   it, binds it or captures it needs the reference a take parameter brings. The sets are found
   together, starting from every candidate and removing those that fail, until none does.

   Left alone: a function with a mut parameter, through which the caller's variable could change
   under the borrow; and a function that returns a constructor holding a call of itself, which
   runs as a loop (section 9.5) whose turns pass new values to take parameters, something a
   read-only parameter cannot be given. *)
let note_demotions st =
  let prog = st.prog in
  let methods = Hashtbl.create 32 and valued = Hashtbl.create 32 in
  List.iter (fun (im : impl_info) -> List.iter (fun (_, g) -> Hashtbl.replace methods g ()) im.imethods_) prog.impls;
  let bodies =
    Hashtbl.fold (fun _ (f : tfn) acc -> f.fbody :: acc) prog.fns []
    @ List.map (fun (_, b, _, _, _) -> b) prog.tests @ List.map (fun (l : lambda) -> l.lbody) prog.lambdas in
  List.iter (walk_texpr (fun (x : texpr) -> match x.e with XFnRef (u, _) -> Hashtbl.replace valued u () | _ -> ()) (fun _ -> ())) bodies;
  let loop_shaped u (body : texpr) =
    let is_self (x : texpr) = match x.e with XCall (CFn (g, _), _, _) -> g = u | _ -> false in
    let found = ref false in
    let rec tail (x : texpr) = match x.e with
      | XIf (_, a, b) -> tail a; tail b
      | XMatch (_, arms) -> List.iter (fun a -> tail a.body) arms
      | XBlock (_, v) -> tail v
      | XVariant (_, _, _, fs) -> if List.exists is_self fs then found := true
      | _ -> () in
    tail body;
    walk_texpr (fun _ -> ()) (fun s -> match s.st with SReturn x -> tail x | _ -> ()) body;
    !found in
  let candidates = ref [] in
  Hashtbl.iter (fun u (f : tfn) ->
      let sg = f.fsig in
      if not sg.sexport && prog.main <> Some u && sg.slend = None && not (Hashtbl.mem methods u) && not (Hashtbl.mem valued u)
         && not (List.exists (fun (m, _, _, _) -> m = MMut) sg.sparams) && not (loop_shaped u f.fbody) then
        List.iteri (fun i ((v : var), (m, _, _, _)) ->
            if m = MTake && not v.vcell && not v.vcaptured then candidates := (u, i, v, f.fbody) :: !candidates)
          (List.combine f.fparams sg.sparams)) prog.fns;
  List.iter (fun (u, i, _, _) -> Hashtbl.replace st.demoted (u, i) ()) !candidates;
  let only_read (v : var) (body : texpr) =
    let derived = Hashtbl.create 8 in
    Hashtbl.replace derived v.vid ();
    let ok = ref true in
    let rec root (x : texpr) = match x.e with
      | XVar w -> Hashtbl.mem derived w.vid
      | XField (b, _, _) | XTupleGet (b, _) -> root b
      | _ -> false in
    let rec bound = function
      | TPVar w -> Hashtbl.replace derived w.vid ()
      | TPVariant (_, _, _, ps) | TPStruct (_, _, ps) | TPTuple ps -> List.iter bound ps
      | TPErrType (_, p) -> bound p
      | TPWild | TPLit _ -> () in
    let captures (lam : lambda) = if List.exists (fun (w : var) -> Hashtbl.mem derived w.vid) lam.lcaps then ok := false in
    (* read: the value of x is looked at where it stands, and not kept *)
    let rec go read (x : texpr) =
      match x.e with
      | XVar w -> if Hashtbl.mem derived w.vid && not read then ok := false
      | XLit _ | XNone | XFnRef _ -> ()
      | XField (b, _, _) | XTupleGet (b, _) -> go true b
      | XIndex (a, i) -> go true a; go true i
      | XSlice (a, lo, hi) -> go true a; go true lo; go true hi
      | XBin (_, a, b) -> go true a; go true b
      | XNeg a | XNot a | XConv a -> go true a
      | XFStr parts -> List.iter (go true) parts
      | XCall (cl, args, _) ->
          (match cl with CClosure f -> go true f | _ -> ());
          List.iteri (fun i a ->
              match a.amode, cl with
              | MBorrow, _ -> go true a.a
              | MTake, CFn (g, _) when Hashtbl.mem st.demoted (g, i) -> go true a.a
              | _ -> go false a.a) args
      | XIf (c, a, b) -> go true c; go read a; go read b
      | XBlock (ss, value) -> List.iter stmt ss; go read value
      | XMatch (s, arms) ->
          go true s;
          if root s then List.iter (fun a -> bound a.pat) arms;
          List.iter (fun a -> Option.iter (go true) a.guard; go read a.body) arms
      | XLambda lam -> captures lam; go false lam.lbody
      | XTuple es | XArray es | XStruct (_, _, es) | XVariant (_, _, _, es) -> List.iter (go false) es
      | XTry a | XFail a | XPack a -> go false a
      | XComp (b, cs) ->
          go false b;
          List.iter (fun cp ->
              (match cp.csrc with IRange (a, b) -> go true a; go true b | IArray (a, _) -> go true a);
              Option.iter (go true) cp.ccond) cs
    and stmt (s : tstmt) =
      match s.st with
      | SLet (_, e) | SVar (_, e) | SReturn e | SLend e | SCheck e -> go false e
      | SExpr e | SAssert (e, _) | SAssertFails (_, e) -> go true e
      | SAssign (p, e) ->
          if Hashtbl.mem derived p.root.vid then ok := false;
          Option.iter (go false) p.via;
          List.iter (function PIndex i -> go true i | _ -> ()) p.path;
          go false e
      | SBreak | SContinue -> ()
      | SWhile (c, b) -> go true c; go true b
      | SFor (_, it, b) ->
          (match it with IRange (a, b) -> go true a; go true b | IArray (a, _) -> go true a);
          go true b
      | SLocalFn (_, lam) -> captures lam; go false lam.lbody
    in
    go false body;
    !ok in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (u, i, v, body) ->
        if Hashtbl.mem st.demoted (u, i) && not (only_read v body) then (Hashtbl.remove st.demoted (u, i); changed := true)) !candidates
  done

(* the generated functions that verify.ml reads: helpers, functions, and the entries main calls *)
let verify_text st =
  Buffer.contents st.helpers ^ Buffer.contents st.funcs
  ^ String.concat "" (Hashtbl.fold (fun name _ acc -> match Hashtbl.find_opt st.entry_defs name with Some (_, def) -> def :: acc | None -> acc) st.entries [])

let rec emit ?(check_only = false) ?explain ?(profile = false) (prog : tprog) ~debug : string =
  let st = {
    prog; fwd = Buffer.create 1024; typedefs = Buffer.create 4096; boxed_bodies = Buffer.create 1024;
    protos = Buffer.create 4096; helpers = Buffer.create 4096; funcs = Buffer.create 16384;
    defined = Hashtbl.create 64; pending_boxed = Queue.create (); instances = Hashtbl.create 64;
    queue = Queue.create (); strlits = Hashtbl.create 64; dps = ref None; reuse = ref []; movable = ref []; pinned = Hashtbl.create 32; self_sliced = Hashtbl.create 16; view_vars = Hashtbl.create 16; loops = Hashtbl.create 64; in_main = ref false; entries = Hashtbl.create 8; entry_defs = Hashtbl.create 32; errtypes = Hashtbl.create 8;
    layouts = Hashtbl.create 64; marking = ref false; cur = ref (Syntax.noloc, ""); marks = ref []; excused = ref []; records = ref []; names = ref []; demoted = Hashtbl.create 16; explain = explain <> None; profile;
    debug; counter = 0 }
  in
  note_demotions st;
  let main_u = match prog.main with
    | Some m -> m
    | None -> if check_only then "" else raise (Unsupported ("no main function", Syntax.noloc)) in
  (* a noalloc or inplace function is checked whether or not main reaches it; one with type
     parameters is checked in each form the program uses *)
  let checked = List.filter (fun u -> let sg = (Hashtbl.find prog.fns u).fsig in sg.smods <> [] && sg.stparams = []) prog.fn_order in
  if check_only then begin
    List.iter (fun u -> ignore (!request_instance st u [])) (checked @ (if main_u = "" then [] else [ main_u ]));
    let rec drain () =
      if not (Queue.is_empty st.queue) then begin
        let cname, uname, tys = Queue.pop st.queue in
        compile_instance st cname uname tys;
        flush_boxed st;
        drain ()
      end in
    drain ();
    Verify.run ~records:!(st.records) ~names:!(st.names) ~text:(verify_text st);
    Option.iter (fun out -> out := Verify.explain ~records:!(st.records) ~text:(verify_text st)) explain;
    raise Exit
  end;
  let main_sg = (Hashtbl.find prog.fns main_u).fsig in
  let main_c = !request_instance st main_u [] in
  List.iter (fun u -> ignore (!request_instance st u [])) checked;
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
  Verify.run ~records:!(st.records) ~names:!(st.names) ~text:(verify_text st);
  Option.iter (fun out -> out := Verify.explain ~records:!(st.records) ~text:(verify_text st)) explain;
  let out = Buffer.create 65536 in
  pr out "/* Generated by the Starnite compiler. */\n";
  if debug then pr out "#define STN_DEBUG 1\n";
  if profile then pr out "#ifndef STN_PROFILE_COPIES\n#define STN_PROFILE_COPIES 1\n#endif\n";
  pr out "#include <stdint.h>\n#include <stdio.h>\n#include <math.h>\n#include \"stn_runtime.h\"\n\n";
  Buffer.add_buffer out st.fwd;
  Buffer.add_buffer out st.typedefs;
  Buffer.add_buffer out st.boxed_bodies;
  pr out "\n";
  Buffer.add_buffer out st.protos;
  Hashtbl.iter (fun name _ ->
      match Hashtbl.find_opt st.entry_defs name with
      | Some (proto, _) -> Buffer.add_string out proto
      | None -> ()) st.entries;
  pr out "\n";
  Buffer.add_buffer out st.helpers;
  pr out "\n";
  if profile then begin
    (* From here on, whatever can copy a shared value or raise a count first names the line it is
       on. The helpers above are left alone: they work for the statement that called them. *)
    let at name = pr out "#define %s(...) (stn_profile_at(__FILE__, __LINE__), %s(__VA_ARGS__))\n" name name in
    List.iter at [ "stn_array_make_unique"; "stn_array_copy_for_write"; "stn_array_push_slow"; "stn_array_reserve"; "stn_array_extend";
                   "stn_array_insert"; "stn_array_remove"; "stn_array_clear"; "stn_array_sort_i64"; "stn_array_reverse_i64";
                   "stn_map_make_unique_for_write"; "stn_map_put"; "stn_map_slot"; "stn_map_slot_ref"; "stn_map_remove"; "stn_map_clear" ];
    (* The runtime reports a count where one is raised, and a view where one is copied: keeping a
       string that is inline does neither, and keeping a struct raises one count for each counted
       field. These only say where. *)
    List.iter at ([ "stn_dup"; "stn_error_dup"; "stn_str_dup" ] @ Verify.dup_helpers (Buffer.contents st.helpers))
  end;
  Buffer.add_buffer out st.funcs;
  Hashtbl.iter (fun name _ ->
      match Hashtbl.find_opt st.entry_defs name with
      | Some (_, def) -> Buffer.add_string out def
      | None -> ()) st.entries;
  Buffer.add_buffer out show_err2;
  pr out "\nint main(void) {\n  stn_runtime_init();\n";
  if sig_can_fail main_sg then begin
    pr out "  StnUnit r; StnError e;\n  if (%s(&r, &e)) {\n" main_c;
    pr out "    StnStr s = stn_show_error(e);\n    fflush(stdout);\n";
    pr out "    stn_runtime_flush_for_error();\n    fprintf(stderr, \"error: %%.*s\\n\", (int)stn_str_len(s), stn_str_ptr(&s));\n";
    pr out "    STN_STR_DROP(s); stn_error_drop(e);\n    stn_runtime_exit(1);\n  }\n"
  end else pr out "  %s();\n" main_c;
  pr out "  stn_runtime_exit(0);\n  return 0;\n}\n";
  Buffer.contents out

(* The checks of section 9.6 alone, for the commands that write no C. A program the C backend
   does not cover yet is left unchecked. *)
and check ?explain (prog : tprog) : unit =
  if explain <> None || Hashtbl.fold (fun _ (f : tfn) acc -> acc || f.fsig.smods <> []) prog.fns false then
    try ignore (emit ~check_only:true ?explain prog ~debug:true) with Exit | Unsupported _ -> ()
