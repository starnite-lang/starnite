(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Passes 2, 3, 5 and 6: names, types, effects and call-site checks (sections 3 to 7). *)

open Syntax
open Types

let err = Syntax.error

(* ---------- global tables ---------- *)

type tables = {
  decls : (string, tdecl) Hashtbl.t;
  variants : (string, string * int) Hashtbl.t;         (* variant name -> type, index *)
  fns : (string, fsig) Hashtbl.t;                       (* unique name -> sig *)
  by_name : (string, string list) Hashtbl.t;            (* display name -> unique names *)
  bodies : (string, Syntax.fn_def * (string * ty) list) Hashtbl.t;  (* unique -> def, Self binding *)
  traits : (string, trait_info) Hashtbl.t;
  mutable impls : impl_info list;
  consts : (string, Syntax.expr * ty option * loc) Hashtbl.t;
  typed_consts : (string, texpr) Hashtbl.t;
  mutable lambdas : lambda list;
  mutable final_pass : bool;
  mutable decl_errors : (string * loc * string) list;
}

let builtin_prefix = "builtin:"
let is_builtin n = String.length n > 8 && String.sub n 0 8 = builtin_prefix

let prim_names =
  [ ("Int", TInt IInt); ("I8", TInt I8); ("I16", TInt I16); ("I32", TInt I32); ("I64", TInt I64);
    ("U8", TInt U8); ("U16", TInt U16); ("U32", TInt U32); ("U64", TInt U64);
    ("Float", TFloat); ("F32", TF32); ("Bool", TBool); ("Char", TChar); ("Unit", TUnit);
    ("Str", TStr); ("Duration", TDur); ("Bytes", TBytes) ]

(* The "head" of a type, used for overloading on the first parameter (section 4.7). *)
let rec head t =
  match repr t with
  | TInt k -> ikind_name k
  | TFloat -> "Float" | TF32 -> "F32" | TBool -> "Bool" | TChar -> "Char" | TUnit -> "Unit"
  | TStr -> "Str" | TDur -> "Duration" | TBytes -> "Bytes"
  | TArray _ -> "Array"
  | TTuple _ -> "(,)"
  | TNamed (n, _) -> n
  | TFn _ -> "fn"
  | TParam _ -> "_param"
  | TVar _ -> "_"
  | TNever -> "_"
  | TErr _ -> "_err"

(* ---------- syntax types to types ---------- *)

let rec conv_ty tb (tps : string list) (self : ty option) (t : Syntax.ty) : ty =
  match t with
  | TyPath ([ "Self" ], [], l) -> (
      match self with Some s -> s | None -> err "E0101" l "Self is only valid inside a trait or impl")
  | TyPath ([ n ], [], _) when List.mem n tps -> TParam n
  | TyPath ([ n ], args, l) -> (
      match List.assoc_opt n prim_names with
      | Some p -> if args <> [] then err "E0102" l "type %s takes no type arguments" n else p
      | None ->
          if n = "Array" then
            match args with [ a ] -> TArray (conv_ty tb tps self a) | _ -> err "E0201" l "Array takes one type argument"
          else
            match Hashtbl.find_opt tb.decls n with
            | Some d ->
                if List.length d.dparams <> List.length args then
                  err "E0201" l "type %s takes %d type argument(s), found %d" n (List.length d.dparams) (List.length args);
                let args = List.map (conv_ty tb tps self) args in
                (match d.dbody with
                 | DAlias a -> subst (List.combine d.dparams args) a
                 | _ -> TNamed (n, args))
            | None -> err "E0101" l "unknown type '%s'" n)
  | TyPath (p, _, l) -> err "E0101" l "unknown type '%s' (modules arrive with imports)" (String.concat "." p)
  | TyAny (n, _, l) -> err "E0230" l "trait values (any %s) are not implemented yet" n
  | TyFn (ps, ret, effs, _) ->
      let fps = List.map (fun (m, t) -> (m, conv_ty tb tps self t)) ps in
      let fret = match ret with Some r -> conv_ty tb tps self r | None -> TUnit in
      let feff =
        match effs with
        | None -> poly_eff
        | Some es -> conv_effects tb tps self es
      in
      TFn { fps; fret; feff }
  | TyTuple ([], _) -> TUnit
  | TyTuple (ts, _) -> TTuple (List.map (conv_ty tb tps self) ts)
  | TyOpt (t, _) -> opt (conv_ty tb tps self t)
  | TyQual (_, t, _) -> conv_ty tb tps self t   (* iso/frozen/unique: milestone 2 and 6 *)

and conv_effects tb tps self es =
  List.fold_left
    (fun e t ->
      match t with
      | TyPath ([ "pure" ], [], _) -> e
      | TyPath ("io" :: _, [], _) -> { e with io = true }
      | TyPath ([ ("alloc" | "div" | "async") ], [], _) -> e
      | TyPath ([ "lock" ], _, _) -> e
      | _ -> { e with errs = e.errs @ [ conv_ty tb tps self t ] })
    no_eff es

(* ---------- trait resolution ---------- *)

(* One-way match of an impl pattern against a concrete type, binding impl parameters. *)
let rec match_ty (ps : string list) (s : (string * ty) list ref) pat t =
  match (repr pat, repr t) with
  | TParam n, t when List.mem n ps -> (
      match List.assoc_opt n !s with
      | Some b -> ty_equal b t || (match repr b, t with _ -> false)
      | None -> s := (n, t) :: !s; true)
  | TArray a, TArray b -> match_ty ps s a b
  | TTuple xs, TTuple ys | TNamed (_, xs), TNamed (_, ys) ->
      (match (repr pat, repr t) with
       | TNamed (n, _), TNamed (m, _) when n <> m -> false
       | _ -> List.length xs = List.length ys && List.for_all2 (match_ty ps s) xs ys)
  | a, b -> ty_equal a b

type resolution =
  | RImpl of string * ty list        (* global fn, its type arguments *)
  | RPrim                            (* built into the backends *)
  | RDerived                         (* derived structurally (Eq, Show on tuples) *)

let prim_traits t =
  match repr t with
  | TInt _ | TFloat | TF32 -> [ "Eq"; "Ord"; "Show"; "Add"; "Sub"; "Mul"; "Div"; "Default"; "Copy"; "Hash" ]
  | TBool | TChar -> [ "Eq"; "Ord"; "Show"; "Default"; "Copy"; "Hash" ]
  | TUnit -> [ "Eq"; "Show"; "Copy" ]
  | TStr -> [ "Eq"; "Ord"; "Show"; "Add"; "Default"; "Hash" ]
  | TDur | TBytes -> [ "Eq"; "Ord"; "Show"; "Add"; "Sub"; "Copy" ]
  | _ -> []

let rec find_impl tb ?(bounds = []) trait (targs : ty list) self : resolution option =
  let self = repr self in
  match self with
  | TParam p -> (
      (* a bound of the enclosing generic function *)
      match List.assoc_opt p bounds with
      | Some bs when List.exists (fun (tr, _) -> tr = trait) bs -> Some RPrim
      | _ -> None)
  | _ ->
      if List.mem trait (prim_traits self) then begin
        (* arithmetic on primitives needs the same type on both sides *)
        match targs with
        | [ r ] when List.mem trait [ "Add"; "Sub"; "Mul"; "Div" ] -> if ty_equal r self then Some RPrim else None
        | _ -> Some RPrim
      end
      else begin
        let cands =
          List.filter_map
            (fun im ->
              if im.itrait_ <> trait then None
              else
                let ps = List.map fst im.itparams in
                let s = ref [] in
                if match_ty ps s im.ifor_ self
                   && (List.length targs = List.length im.itargs_
                       && List.for_all2 (fun p a -> match_ty ps s p a || (match repr a with TVar _ -> true | _ -> false)) im.itargs_ targs)
                then
                  (* impl bounds must hold too *)
                  let ok =
                    List.for_all
                      (fun (p, bs) ->
                        match List.assoc_opt p !s with
                        | None -> true
                        | Some t -> List.for_all (fun (tr, ta) -> find_impl tb ~bounds tr (List.map (subst !s) ta) t <> None) bs)
                      im.itparams
                  in
                  if ok then Some (im, !s) else None
                else None)
            tb.impls
        in
        match cands with
        | (im, s) :: _ ->
            let fname = try List.assoc "__any" im.imethods_ with Not_found -> "" in
            ignore fname;
            Some (RImpl ("", List.map (fun (p, _) -> try List.assoc p s with Not_found -> TUnit) im.itparams))
        | [] -> derive tb ~bounds trait self
      end

and derive tb ~bounds trait self =
  let all_fields f =
    match repr self with
    | TArray t -> f t
    | TTuple ts -> List.for_all f ts
    | TNamed (n, args) -> (
        match Hashtbl.find_opt tb.decls n with
        | Some d -> (
            let s = List.combine d.dparams args in
            match d.dbody with
            | DStruct fs -> List.for_all (fun fi -> f (subst s fi.fty)) fs
            | DData vs -> List.for_all (fun v -> List.for_all (fun fi -> f (subst s fi.fty)) v.vfields) vs
            | DAlias _ -> false)
        | None -> false)
    | _ -> false
  in
  let visiting = ref [] in
  let rec has t =
    let key = show_ty t in
    if List.mem key !visiting then true
    else begin
      visiting := key :: !visiting;
      find_impl tb ~bounds trait [] t <> None
    end
  in
  match trait with
  | "Eq" | "Hash" -> (
      match repr self with
      | TArray _ | TTuple _ | TNamed _ ->
          visiting := [ show_ty self ];
          if all_fields has then Some RDerived else None
      | _ -> None)
  | "Show" -> (
      match repr self with
      | TTuple ts -> if List.for_all has ts then Some RDerived else None
      | _ -> None)
  | "Copy" -> None
  | _ -> None

(* The global function implementing [meth] of [trait] for [self]. *)
let rec impl_method tb trait targs meth self = impl_method_in tb.impls trait targs meth self

and impl_method_in impls trait (targs : ty list) meth self : (string * ty list) option =
  let self = repr self in
  let cands =
    List.filter_map
      (fun im ->
        if im.itrait_ <> trait then None
        else
          let ps = List.map fst im.itparams in
          let s = ref [] in
          if match_ty ps s im.ifor_ self
             && List.length targs = List.length im.itargs_
             && List.for_all2 (fun p a -> match_ty ps s p a) im.itargs_ targs
          then
            match List.assoc_opt meth im.imethods_ with
            | Some f -> Some (f, List.map (fun (p, _) -> try List.assoc p !s with Not_found -> TUnit) im.itparams)
            | None -> None
          else None)
      impls
  in
  match cands with c :: _ -> Some c | [] -> None

(* ---------- function context ---------- *)

type lamrec = { mutable caps : var list }

type frame = { mutable vars : (string * var) list; lam : lamrec option }

type fctx = {
  tb : tables;
  mutable frames : frame list;
  tparams : (string * (string * ty list) list) list;
  mutable ret : ty;
  mutable errs : ty list;           (* collected errors of the current function or try *)
  mutable io : bool;
  mutable in_try : int;
  mutable loops : int;
  declared : ty list option;        (* declared error list, if any *)
  mutable obligations : (ty * string * ty list * loc) list;
  mutable unsolved : (ty * loc) list;
  mutable moved : (int * loc) list;        (* variables moved by an explicit take (section 4.2) *)
  mutable lent : (int * loc) list;         (* roots iterated by an enclosing 'for ... in mut' *)
  closure_caps : (int, var list) Hashtbl.t;  (* captures of closures bound to names *)
  fname : string;
  self_ty : ty option;
}

let push_frame c ?lam () = c.frames <- { vars = []; lam } :: c.frames
let pop_frame c = c.frames <- List.tl c.frames

let bind c (v : var) l =
  match c.frames with
  | f :: _ ->
      if List.mem_assoc v.vname f.vars && v.vname <> "_" then
        err "E0101" l "'%s' is already defined in this block; shadowing is allowed only in an inner block" v.vname;
      f.vars <- (v.vname, v) :: f.vars
  | [] -> assert false

let lookup c name : var option =
  let rec go crossed = function
    | [] -> None
    | f :: rest -> (
        match List.assoc_opt name f.vars with
        | Some v ->
            List.iter
              (fun lr ->
                if not (List.memq v lr.caps) then lr.caps <- lr.caps @ [ v ];
                v.vcaptured <- true;
                if v.vmut then v.vcell <- true)
              crossed;
            Some v
        | None -> go (match f.lam with Some lr -> lr :: crossed | None -> crossed) rest)
  in
  go [] c.frames

let all_names c = List.concat_map (fun f -> List.map fst f.vars) c.frames

(* Edit distance for "did you mean" hints (section 19.2). *)
let edit_distance a b =
  let n = String.length a and m = String.length b in
  let d = Array.make_matrix (n + 1) (m + 1) 0 in
  for i = 0 to n do d.(i).(0) <- i done;
  for j = 0 to m do d.(0).(j) <- j done;
  for i = 1 to n do
    for j = 1 to m do
      let c = if a.[i - 1] = b.[j - 1] then 0 else 1 in
      d.(i).(j) <- min (min (d.(i - 1).(j) + 1) (d.(i).(j - 1) + 1)) (d.(i - 1).(j - 1) + c)
    done
  done;
  d.(n).(m)

let unknown_name c l name =
  let cands = all_names c @ List.of_seq (Hashtbl.to_seq_keys c.tb.by_name) in
  let best =
    List.fold_left
      (fun acc n ->
        let dd = edit_distance name n in
        if dd <= max 1 (String.length name / 3) then
          match acc with Some (_, d0) when d0 <= dd -> acc | _ -> Some (n, dd)
        else acc)
      None cands
  in
  match best with
  | Some (n, _) -> err "E0101" l "unknown name '%s'; did you mean '%s'?" name n
  | None -> err "E0101" l "unknown name '%s'" name

let mismatch l expected found =
  err "E0201" l "expected %s, found %s" (show_ty expected) (show_ty found)

let unify_at l expected found =
  try unify expected found with Mismatch -> mismatch l expected found

let mk e ty l = { e; ty; l }
let unit_e l = mk (XLit LUnit) TUnit l

(* ---------- effects ---------- *)

let mem_ty t ts = List.exists (ty_equal t) ts

let add_err_set c (es : ty list) : ty list =
  List.iter (fun e -> if not (mem_ty e c.errs) then c.errs <- c.errs @ [ e ]) es;
  es

(* Errors raised by a call: added to the current set, with From conversions when the
   enclosing function declares its errors (section 5.4). *)
let propagate c l (es : ty list) : conv list =
  let es = List.concat_map (fun e -> match repr e with TErr ts -> ts | _ -> [ e ]) (List.map zonk es) in
  if c.in_try > 0 then (ignore (add_err_set c es); [])
  else
    match c.declared with
    | None -> ignore (add_err_set c es); []
    | Some decl ->
        List.concat_map
          (fun e ->
            if mem_ty e decl then (ignore (add_err_set c [ e ]); [])
            else begin
              let fits =
                List.filter_map
                  (fun d -> match impl_method c.tb "From" [ e ] "from" d with Some (f, _) -> Some (d, f) | None -> None)
                  decl
              in
              match fits with
              | [ (d, f) ] -> ignore (add_err_set c [ d ]); [ { cfrom = e; cfn = f; cto = d } ]
              | [] ->
                  if c.tb.final_pass then
                    err "E0501" l "this call can fail with %s, which '%s' does not list" (show_ty e) c.fname
                  else []
              | _ -> err "E0520" l "more than one From conversion fits %s; capture it with try" (show_ty e)
            end)
          es

let add_eff c l (e : eff) : conv list =
  if e.io then c.io <- true;
  propagate c l e.errs

(* ---------- literals ---------- *)

let int_fits k (s : string) l =
  let neg = String.length s > 0 && s.[0] = '-' in
  let body = if neg then String.sub s 1 (String.length s - 1) else s in
  let v =
    try
      if String.length body > 2 && (body.[1] = 'b' || body.[1] = 'B') then
        Int64.of_string ("0b" ^ String.sub body 2 (String.length body - 2))
      else Int64.of_string body
    with _ -> (
      try Int64.of_string ("0u" ^ body) with _ -> err "E0201" l "integer literal %s is too large" s)
  in
  (* v is the magnitude; for U64 it may have the top bit set *)
  let big = Int64.compare v 0L < 0 in
  let ok =
    match k with
    | U64 -> not neg || v = 0L
    | IInt | I64 -> if neg then (not big) || v = Int64.min_int else not big
    | _ ->
        let bits = ikind_bits k in
        if big then false
        else if ikind_signed k then
          if neg then Int64.compare v (Int64.shift_left 1L (bits - 1)) <= 0
          else Int64.compare v (Int64.shift_left 1L (bits - 1)) < 0
        else (not neg || v = 0L) && Int64.compare v (Int64.shift_left 1L bits) < 0
  in
  if not ok then err "E0201" l "integer literal %s does not fit in %s" s (ikind_name k)

(* ---------- expressions ---------- *)

let rec is_place (e : Syntax.expr) =
  match e.d with
  | Name _ -> true
  | Field (b, _) -> is_place b
  | Bracket (b, [ BExpr { d = Range _; _ } ]) -> false
  | Bracket (b, [ _ ]) -> is_place b
  | _ -> false

let lookup_fns c name = try Hashtbl.find c.tb.by_name name with Not_found -> []

let instantiate (sg : fsig) =
  let s = List.map (fun (p, _) -> (p, fresh ())) sg.stparams in
  (s, List.map (fun (m, n, t, d) -> (m, n, subst s t, d)) sg.sparams, subst s sg.sret,
   { sg.seff with errs = List.map (subst s) sg.seff.errs })

let defaults_table : (string, Syntax.expr option list) Hashtbl.t = Hashtbl.create 16

let check_not_lent c l (v : var) =
  match List.assoc_opt v.vid c.lent with
  | Some (fl : loc) ->
      err "E0323" l "'%s' is lent element by element by the 'for ... in mut' at line %d; the loop body cannot use it" v.vname fl.line
  | None -> ()

let union_moved a b = a @ List.filter (fun (id, _) -> not (List.mem_assoc id a)) b

(* a variable from outside a loop, moved inside it, would be used again on the next pass *)
let loop_moves c before =
  let declared_outside id = List.exists (fun f -> List.exists (fun (_, v) -> v.vid = id) f.vars) c.frames in
  List.iter
    (fun (id, (l : loc)) ->
      if not (List.mem_assoc id before) && declared_outside id then
        err "E0302" l "this 'take' is inside a loop, so the next pass would use the moved value")
    c.moved
let lambda_counter = ref 0

let rec infer c (e : Syntax.expr) : texpr = check_or_infer c e None

and check c (e : Syntax.expr) (expected : ty) : texpr =
  let te = check_or_infer c e (Some expected) in
  coerce c te expected

(* Unify, applying the T -> T? coercion of section 5.3. *)
and coerce c (te : texpr) expected : texpr =
  match (repr expected, repr te.ty) with
  | _, TNever -> { te with ty = expected }
  | TNamed ("Option", [ inner ]), found
    when (match found with TNamed ("Option", _) | TVar _ -> false | _ -> true) ->
      (try unify expected found; te
       with Mismatch ->
         unify_at te.l inner te.ty;
         mk (XVariant ("Option", [ inner ], 1, [ te ])) expected te.l)
  | _ ->
      unify_at te.l expected te.ty;
      eff_check te.l expected te.ty;
      te

(* Unification ignores effects, so check them separately, through every type that can
   hold a function (section 7.2): a function with more effects may not be used where
   one with fewer is expected. Parameters are contravariant. *)
and eff_check ?(invariant = false) l (expected : ty) (found : ty) =
  match (repr expected, repr found) with
  | TFn fe, TFn ff ->
      let sub (a : eff) (b : eff) =
        (* every effect of b must be allowed by a *)
        if not (a.poly || b.poly) then begin
          if b.io && not a.io then
            err "E0503" l "this function performs io, which the expected type %s does not allow" (show_ty expected);
          List.iter
            (fun x -> if not (mem_ty x a.errs) then
                err "E0501" l "this function can fail with %s, which the expected type %s does not allow" (show_ty x) (show_ty expected))
            b.errs
        end
      in
      sub fe.feff ff.feff;
      (* through a mut argument the callee can store its own functions in the caller's
         place, so the effects must be exactly the same *)
      if invariant && not (fe.feff.poly || ff.feff.poly)
         && (fe.feff.io <> ff.feff.io || List.exists (fun x -> not (mem_ty x ff.feff.errs)) fe.feff.errs) then
        err "E0503" l "a mut argument must have exactly the parameter's effects: expected %s, found %s" (show_ty expected) (show_ty found);
      if List.length fe.fps = List.length ff.fps then
        List.iter2 (fun (_, pe) (_, pf) -> eff_check ~invariant l pf pe) fe.fps ff.fps;
      eff_check ~invariant l fe.fret ff.fret
  | TArray a, TArray b -> eff_check ~invariant l a b
  | TTuple xs, TTuple ys | TNamed (_, xs), TNamed (_, ys) | TErr xs, TErr ys ->
      if List.length xs = List.length ys then List.iter2 (eff_check ~invariant l) xs ys
  | _ -> ()

and check_or_infer c (e : Syntax.expr) (expected : ty option) : texpr =
  let l = e.loc in
  let exp = match expected with Some t -> Some (repr t) | None -> None in
  match e.d with
  | Lit (LInt s) -> (
      match exp with
      | Some (TInt k) -> int_fits k s l; mk (XLit (LInt s)) (TInt k) l
      | Some (TFloat | TF32 as t) -> mk (XLit (LFloat (float_of_string s))) t l
      | _ -> int_fits IInt s l; mk (XLit (LInt s)) (TInt IInt) l)
  | Lit (LFloat f) -> (
      match exp with Some TF32 -> mk (XLit (LFloat f)) TF32 l | _ -> mk (XLit (LFloat f)) TFloat l)
  | Lit (LStr s) -> mk (XLit (LStr s)) TStr l
  | Lit (LChar ch) -> mk (XLit (LChar ch)) TChar l
  | Lit (LBool b) -> mk (XLit (LBool b)) TBool l
  | Lit LUnit -> unit_e l
  | Lit (LDur (n, u)) ->
      let t = if List.mem u [ "b"; "kib"; "mib"; "gib" ] then TBytes else TDur in
      (* the scaled value (nanoseconds or bytes) must fit in 64 bits *)
      let scaled = Values.dur_value n u in
      let unit_ = Values.dur_value 1L u in
      if Int64.compare n 0L < 0 || (unit_ > 1L && Int64.compare n (Int64.div Int64.max_int unit_) > 0) || Int64.compare scaled 0L < 0 then
        err "E0201" l "%Ld%s does not fit in %s" n u (show_ty t);
      mk (XLit (LDur (n, u))) t l
  | FStr parts ->
      let ps =
        List.map
          (function
            | FLit s -> mk (XLit (LStr s)) TStr l
            | FExpr e -> show_expr c (infer c e))
          parts
      in
      mk (XFStr ps) TStr l
  | Name n -> infer_name c l n exp
  | Field (b, f) -> infer_field c l b f
  | Call (f, args) -> infer_call c l f args exp
  | Bracket (b, args) -> infer_bracket c l b args exp
  | Tuple es ->
      let ets = match exp with Some (TTuple ts) when List.length ts = List.length es -> List.map Option.some ts | _ -> List.map (fun _ -> None) es in
      let tes = List.map2 (fun e t -> match t with Some t -> check c e t | None -> infer c e) es ets in
      mk (XTuple tes) (TTuple (List.map (fun t -> t.ty) tes)) l
  | ArrayLit es ->
      let elt = match exp with Some (TArray t) -> t | _ -> fresh () in
      if es = [] then c.unsolved <- (elt, l) :: c.unsolved;
      let tes = List.map (fun e -> check c e elt) es in
      mk (XArray tes) (TArray elt) l
  | Comp (body, comps) ->
      push_frame c ();
      let tcs = List.map (fun cp -> check_comp c cp) comps in
      let tb = match exp with Some (TArray t) -> check c body t | _ -> infer c body in
      List.iter (fun _ -> ()) tcs;
      pop_frame c;
      mk (XComp (tb, tcs)) (TArray tb.ty) l
  | BraceLit _ | MapLit _ -> err "E0201" l "Map and Set literals arrive in milestone 2"
  | IfE (cnd, a, b) ->
      let tc = check c cnd TBool in
      let ta = match exp with Some t -> check c a t | None -> infer c a in
      let tb = check c b ta.ty in
      mk (XIf (tc, ta, tb)) (if ta.ty = TNever then tb.ty else ta.ty) l
  | Lambda (ps, body) -> infer_lambda c l ps body exp
  | Unop ("-", { d = Lit (LInt s); _ }) ->
      (* a negative literal is one literal: -128 fits in I8 even though 128 does not *)
      check_or_infer c { e with d = Lit (LInt ("-" ^ s)) } expected
  | Unop ("-", { d = Lit (LFloat f); _ }) -> check_or_infer c { e with d = Lit (LFloat (-.f)) } expected
  | Unop ("-", a) ->
      let ta = match exp with Some t when is_numeric t -> check c a t | _ -> infer c a in
      if not (is_numeric ta.ty) then err "E0201" l "unary - needs a number, found %s" (show_ty ta.ty);
      mk (XNeg ta) ta.ty l
  | Unop ("not", a) -> let ta = check c a TBool in mk (XNot ta) TBool l
  | Unop ("try", a) ->
      let saved = c.errs in
      c.errs <- [];
      c.in_try <- c.in_try + 1;
      let ta = infer c a in
      c.in_try <- c.in_try - 1;
      let es = c.errs in
      c.errs <- saved;
      let et = match es with [ e ] -> e | es -> TErr es in
      mk (XTry ta) (TNamed ("Result", [ ta.ty; et ])) l
  | Unop (op, _) -> err "E0201" l "'%s' arrives in a later milestone" op
  | Binop (op, a, b) -> infer_binop c l op a b exp
  | Range _ -> err "E0201" l "a range is only valid in a for loop or a slice"

and show_expr c (te : texpr) : texpr =
  match repr te.ty with
  | TStr -> te
  | t ->
      if find_impl c.tb ~bounds:c.tparams "Show" [] t = None && (match t with TVar _ -> false | _ -> true) then
        err "E0204" te.l "%s does not implement Show" (show_ty t);
      if (match t with TVar _ -> true | _ -> false) then c.obligations <- (t, "Show", [], te.l) :: c.obligations;
      mk (XCall (CTrait ("Show", [], "show", te.ty), [ { amode = MBorrow; a = te } ], [])) TStr te.l

and check_comp c (cp : Syntax.comp) : tcomp =
  let src, elt = check_iter c cp.citer MBorrow in
  let p = check_pat c cp.cpat elt false in
  let cond = Option.map (fun e -> check c e TBool) cp.cif in
  { cvar = p; csrc = src; ccond = cond }

and check_iter c (it : Syntax.expr) mode : titer * ty =
  match it.d with
  | Range (a, b) ->
      let ta = infer c a in
      if not (is_int ta.ty) then err "E0201" a.loc "a range needs integers, found %s" (show_ty ta.ty);
      let tb = check c b ta.ty in
      (IRange (ta, tb), ta.ty)
  | _ ->
      let te = infer c it in
      (match repr te.ty with
       | TArray t -> (IArray (te, mode), t)
       | TStr -> err "E0201" it.loc "iterate over chars(s) to visit the characters of a Str"
       | t -> err "E0204" it.loc "%s cannot be iterated; for loops take an Array or a range" (show_ty t))

and infer_name c l n exp : texpr =
  match lookup c n with
  | Some v ->
      (match List.assoc_opt v.vid c.moved with
       | Some ml ->
           err "E0302" l "'%s' is used after 'take %s' at line %d; the value has moved" n n ml.line
       | None -> ());
      check_not_lent c l v;
      mk (XVar v) v.vty l
  | None -> (
      match Hashtbl.find_opt c.tb.variants n with
      | Some (tn, idx) -> construct_variant c l tn idx n [] exp
      | None -> (
          match Hashtbl.find_opt c.tb.typed_consts n with
          | Some te -> te
          | None -> (
              match lookup_fns c n with
              | [ u ] ->
                  let sg = Hashtbl.find c.tb.fns u in
                  let s, ps, ret, eff = instantiate sg in
                  let ty = TFn { fps = List.map (fun (m, _, t, _) -> (m, t)) ps; fret = ret; feff = eff } in
                  (match exp with Some t -> unify_at l t ty | None -> ());
                  mk (XFnRef (u, List.map snd s)) ty l
              | _ :: _ -> err "E0201" l "'%s' is overloaded; call it directly" n
              | [] -> unknown_name c l n)))

and infer_field c l b f : texpr =
  (* qualified variant: Shape.Circle *)
  match b.d with
  | Name tn when lookup c tn = None && Hashtbl.mem c.tb.decls tn -> (
      match Hashtbl.find_opt c.tb.variants f with
      | Some (tn', idx) when tn' = tn -> construct_variant c l tn idx f [] None
      | _ -> err "E0101" l "type %s has no variant %s" tn f)
  | _ ->
      let tb = infer c b in
      field_of c l tb f

and field_of c l (tb : texpr) f : texpr =
  match repr tb.ty with
  | TTuple ts -> (
      match int_of_string_opt f with
      | Some i when i < List.length ts -> mk (XTupleGet (tb, i)) (List.nth ts i) l
      | _ -> err "E0201" l "tuple %s has no field %s" (show_ty tb.ty) f)
  | TNamed (n, args) -> (
      let d = Hashtbl.find c.tb.decls n in
      match d.dbody with
      | DStruct fs -> (
          let s = List.combine d.dparams args in
          let rec find i = function
            | [] -> err "E0201" l "%s has no field '%s'" (show_ty tb.ty) f
            | fi :: rest -> if fi.fname_ = f then mk (XField (tb, i, f)) (subst s fi.fty) l else find (i + 1) rest
          in
          find 0 fs)
      | _ -> err "E0201" l "%s is a data type; use match to read its fields" (show_ty tb.ty))
  | TVar _ -> err "E0201" l "the type of this value must be known before '.%s'; add an annotation" f
  | t -> err "E0201" l "%s has no field '%s'" (show_ty t) f

(* Arguments matched to parameters: positional first, then named, then defaults. *)
and match_args c l (params : (mode * string * ty * Syntax.expr option) list) (args : Syntax.arg list) :
    (mode * string * ty * Syntax.arg option * Syntax.expr option) list =
  let positional = List.filter (fun a -> a.aname = None) args in
  let named = List.filter (fun a -> a.aname <> None) args in
  let np = List.length params in
  if List.length positional > np then
    err "E0203" l "expected %d argument(s), found %d" np (List.length args);
  let rec seen_named = function
    | [] -> ()
    | a :: rest -> if a.aname <> None && List.exists (fun b -> b.aname = None) rest then
          err "E0100" a.aloc "named arguments must follow positional ones"
        else seen_named rest
  in
  seen_named args;
  let res =
    List.mapi
      (fun i (m, n, t, d) ->
        let a = if i < List.length positional then Some (List.nth positional i)
          else List.find_opt (fun a -> a.aname = Some n) named in
        (match a with None when d = None -> err "E0203" l "missing argument '%s'" n | _ -> ());
        (m, n, t, a, d))
      params
  in
  List.iter
    (fun a ->
      match a.aname with
      | Some n when not (List.exists (fun (_, pn, _, _) -> pn = n) params) ->
          err "E0203" a.aloc "no parameter named '%s'" n
      | _ -> ())
    named;
  res

and mutable_place c (e : Syntax.expr) : bool =
  let rec root (e : Syntax.expr) =
    match e.d with
    | Name n -> Some n
    | Field (b, _) -> root b
    | Bracket (b, _) -> root b
    | _ -> None
  in
  is_place e
  && match root e with
     | Some n -> (match lookup c n with Some v -> v.vmut || v.vkind = VParam MMut | None -> false)
     | None -> false

(* Check the arguments of a call against instantiated parameters. *)
and check_args c l ~(receiver : texpr option) params (args : Syntax.arg list) : targ list * eff list =
  let params_rest, recv_targ =
    match (receiver, params) with
    | Some r, (m, _, t, _) :: rest ->
        let r = coerce c r t in
        (rest, [ { amode = m; a = r } ])
    | Some _, [] -> err "E0203" l "this function takes no arguments"
    | None, _ -> (params, [])
  in
  let matched = match_args c l params_rest args in
  let poly_effs = ref [] in
  let targs =
    List.map
      (fun (m, n, t, (a : Syntax.arg option), d) ->
        match a with
        | Some a ->
            (match (m, a.amode) with
             | MMut, Some MMut -> if not (mutable_place c a.aexpr) then
                   err "E0303" a.aloc "'mut' argument must be a mutable place (a var, a mut parameter, or a field or element of one)"
             | MMut, _ -> err "E0304" a.aloc "parameter '%s' is mut; write 'mut' at the call site" n
             | _, Some MMut -> err "E0304" a.aloc "parameter '%s' is not mut" n
             | _ -> ());
            let te = check c a.aexpr t in
            if m = MMut then eff_check ~invariant:true a.aloc t te.ty;
            (match (a.amode, te.e) with
             | Some MTake, XVar v -> c.moved <- (v.vid, a.aloc) :: c.moved
             | Some MTake, _ -> err "E0302" a.aloc "'take' moves a variable; write it before a variable name"
             | _ -> ());
            (match (repr t, repr te.ty) with
             | TFn pf, TFn af when pf.feff.poly && not af.feff.poly -> poly_effs := af.feff :: !poly_effs
             | _ -> ());
            { amode = m; a = te }
        | None -> (
            match d with
            | Some d -> { amode = m; a = check c d t }
            | None -> assert false))
      matched
  in
  (* exclusivity: a mut argument must not overlap another argument (section 4.3) *)
  let all = recv_targ @ targs in
  let rec path (e : texpr) =
    match e.e with
    | XVar v -> Some (v.vid, [])
    | XField (b, i, _) -> Option.map (fun (r, p) -> (r, p @ [ `F i ])) (path b)
    | XTupleGet (b, i) -> Option.map (fun (r, p) -> (r, p @ [ `F i ])) (path b)
    | XIndex (b, _) -> Option.map (fun (r, p) -> (r, p @ [ `I ])) (path b)
    | _ -> None
  in
  let rec prefix a b =
    match (a, b) with
    | [], _ | _, [] -> true
    | `I :: a', `I :: b' -> prefix a' b'
    | `F i :: a', `F j :: b' -> i = j && prefix a' b'
    | _ -> false
  in
  let overlaps (r1, p1) (r2, p2) = r1 = r2 && prefix p1 p2 in
  List.iteri
    (fun i ta ->
      if ta.amode = MMut then
        match path ta.a with
        | Some p ->
            List.iteri
              (fun j tb ->
                if i <> j && tb.amode <> MTake then
                  match path tb.a with
                  | Some q when overlaps p q ->
                      err "E0301" tb.a.l "this argument overlaps a mut argument of the same call; write 'let tmp = ...' first"
                  | _ -> ())
              all;
            List.iteri
              (fun j tb ->
                if i <> j then
                  let caps =
                    match tb.a.e with
                    | XLambda lam -> lam.lcaps
                    | XVar v -> (try Hashtbl.find c.closure_caps v.vid with Not_found -> [])
                    | _ -> []
                  in
                  let (r, _) = p in
                  if List.exists (fun v -> v.vid = r) caps then
                    err "E0305" tb.a.l "this closure captures a variable passed as mut to the same call")
              all
        | None -> ())
    all;
  (all, !poly_effs)

and call_sig c l (u : string) ~receiver (args : Syntax.arg list) exp : texpr =
  let sg = Hashtbl.find c.tb.fns u in
  let s, ps, ret, eff = instantiate sg in
  (match exp with
   | Some t when (match repr ret with TVar _ | TNamed _ | TArray _ | TTuple _ -> true | _ -> false) ->
       (try unify t ret with Mismatch -> ())
   | _ -> ());
  let targs, poly = check_args c l ~receiver ps args in
  let convs = add_eff c l eff @ List.concat_map (add_eff c l) poly in
  (* bounds become obligations *)
  List.iter
    (fun (p, bs) ->
      let t = List.assoc p s in
      List.iter (fun (tr, ta) -> c.obligations <- (t, tr, List.map (subst s) ta, l) :: c.obligations) bs)
    sg.stparams;
  let callee = if is_builtin u then CBuiltin (String.sub u 8 (String.length u - 8), List.map snd s) else CFn (u, List.map snd s) in
  let ret = ret in
  mk (XCall (callee, targs, convs)) ret l

(* Pick an overload by the head of the first argument's type. *)
and pick_overload c l name (cands : string list) (first : texpr option) : string =
  match cands with
  | [ u ] -> u
  | _ -> (
      match first with
      | None -> err "E0201" l "cannot choose between overloads of '%s'" name
      | Some te ->
          let h = head te.ty in
          let ms =
            List.filter
              (fun u ->
                let sg = Hashtbl.find c.tb.fns u in
                match sg.sparams with
                | (_, _, t, _) :: _ -> head t = h
                | [] -> false)
              cands
          in
          match ms with
          | [ u ] -> u
          | [] -> err "E0201" l "no '%s' takes %s as its first argument" name (show_ty te.ty)
          | _ -> err "E0105" l "'%s' matches more than one function" name)

and infer_call c l (f : Syntax.expr) (args : Syntax.arg list) exp : texpr =
  match f.d with
  | Name "fail" when lookup c "fail" = None -> (
      match args with
      | [ a ] ->
          let te = infer c a.aexpr in
          (match repr te.ty with
           | TNamed _ | TErr _ -> ()
           | t -> err "E0201" a.aloc "fail needs a value of an error type, found %s" (show_ty t));
          let convs = propagate c l [ te.ty ] in
          ignore convs;
          (* conversion of a failed value happens through the declared list *)
          let te =
            match c.declared with
            | Some decl when c.in_try = 0 && not (mem_ty te.ty decl) -> (
                match List.filter_map (fun d -> match impl_method c.tb "From" [ te.ty ] "from" d with Some (fn, ta) -> Some (d, fn, ta) | None -> None) decl with
                | [ (d, fn, ta) ] -> mk (XCall (CFn (fn, ta), [ { amode = MBorrow; a = te } ], [])) d te.l
                | _ -> te)
            | _ -> te
          in
          mk (XFail te) TNever l
      | _ -> err "E0203" l "fail takes one argument")
  | Name n when lookup c n = None && List.mem_assoc n prim_names && n <> "Unit" -> (
      (* numeric conversion: Float(n), I32(x) (section 17.1) *)
      let target = List.assoc n prim_names in
      match args with
      | [ a ] ->
          let te = infer c a.aexpr in
          let ok =
            match (repr te.ty, target) with
            | (TInt _ | TFloat | TF32 | TChar | TBool), (TInt _ | TFloat | TF32) -> true
            | TInt _, TChar -> true
            | (TDur | TBytes), TInt _ | TInt _, (TDur | TBytes) -> true
            | _ -> false
          in
          if not ok then err "E0201" l "cannot convert %s to %s" (show_ty te.ty) n;
          mk (XConv te) target l
      | _ -> err "E0203" l "%s(...) takes one argument" n)
  | Name n when lookup c n = None && Hashtbl.mem c.tb.decls n && not (Hashtbl.mem c.tb.variants n) ->
      construct_struct c l n args exp
  | Name n when lookup c n = None && Hashtbl.mem c.tb.variants n ->
      let tn, idx = Hashtbl.find c.tb.variants n in
      construct_variant c l tn idx n args exp
  | Name n when lookup c n = None && lookup_fns c n <> [] ->
      let cands = lookup_fns c n in
      let first =
        if List.length cands > 1 then
          match args with a :: _ -> Some (infer c a.aexpr) | [] -> None
        else None
      in
      let u = pick_overload c l n cands first in
      call_sig c l u ~receiver:None args exp
  | Field (b, m) -> infer_method c l b m args exp
  | _ ->
      (* call of a function value *)
      let tf = infer c f in
      (match repr tf.ty with
       | TFn ft ->
           let ps = List.mapi (fun i (m, t) -> (m, Printf.sprintf "arg%d" i, t, None)) ft.fps in
           let targs, _ = check_args c l ~receiver:None ps args in
           let convs = add_eff c l { ft.feff with poly = false } in
           mk (XCall (CClosure tf, targs, convs)) ft.fret l
       | TVar _ -> err "E0201" l "the type of this function value must be known; add an annotation"
       | t -> err "E0201" l "%s is not a function" (show_ty t))

and construct_struct c l n args exp : texpr =
  let d = Hashtbl.find c.tb.decls n in
  match d.dbody with
  | DStruct fs ->
      let s = List.map (fun p -> (p, fresh ())) d.dparams in
      let ty = TNamed (n, List.map snd s) in
      (match exp with Some t -> (try unify t ty with Mismatch -> ()) | None -> ());
      let defaults = struct_defaults c n in
      let params = List.map2 (fun fi dflt -> (MTake, fi.fname_, subst s fi.fty, dflt)) fs defaults in
      let targs, _ = check_args c l ~receiver:None params args in
      mk (XStruct (n, List.map snd s, List.map (fun a -> a.a) targs)) ty l
  | _ -> err "E0201" l "%s is not a struct" n

and struct_defaults c n : Syntax.expr option list =
  try Hashtbl.find defaults_table n with Not_found -> []

and construct_variant c l tn idx vn (args : Syntax.arg list) exp : texpr =
  let d = Hashtbl.find c.tb.decls tn in
  match d.dbody with
  | DData vs ->
      let v = List.nth vs idx in
      let s = List.map (fun p -> (p, fresh ())) d.dparams in
      let ty = TNamed (tn, List.map snd s) in
      (match exp with
       | Some t -> (try unify t ty with Mismatch -> ())
       | None -> ());
      if v.vfields = [] && args <> [] then err "E0203" l "variant %s takes no arguments" vn;
      let defaults = try Hashtbl.find defaults_table (tn ^ "." ^ vn) with Not_found -> List.map (fun _ -> None) v.vfields in
      let params = List.map2 (fun fi dflt -> (MTake, fi.fname_, subst s fi.fty, dflt)) v.vfields defaults in
      let targs, _ = if v.vfields = [] then ([], []) else check_args c l ~receiver:None params args in
      if v.vfields <> [] && args = [] && List.exists (fun d -> d = None) defaults then
        err "E0203" l "variant %s needs %d argument(s)" vn (List.length v.vfields);
      List.iter (fun (_, t) -> ()) s;
      let te = mk (XVariant (tn, List.map snd s, idx, List.map (fun a -> a.a) targs)) ty l in
      te
  | _ -> err "E0201" l "%s is not a data type" tn

and infer_method c l (b : Syntax.expr) m (args : Syntax.arg list) exp : texpr =
  match b.d with
  (* T.f(args) and Trait.f(args) *)
  | Name tn when lookup c tn = None && Hashtbl.mem c.tb.traits tn ->
      let tr = Hashtbl.find c.tb.traits tn in
      let sg = try List.assoc m tr.trmethods_ with Not_found -> err "E0101" l "trait %s has no method %s" tn m in
      let self = fresh () in
      (match (exp, repr sg.sret) with Some t, TParam "Self" -> unify_at l t self | _ -> ());
      trait_call c l tn [] m sg self None args exp
  | Name tn when lookup c tn = None && Hashtbl.mem c.tb.decls tn && Hashtbl.mem c.tb.variants m ->
      let tn', idx = Hashtbl.find c.tb.variants m in
      if tn' <> tn then err "E0101" l "type %s has no variant %s" tn m;
      construct_variant c l tn idx m args exp
  | Name tn when lookup c tn = None && (Hashtbl.mem c.tb.decls tn || List.mem_assoc tn prim_names) ->
      let cands = lookup_fns c m in
      let ok = List.filter (fun u ->
          let sg = Hashtbl.find c.tb.fns u in
          sg.smodule <> "" && (match sg.sparams with (_, _, t, _) :: _ -> head t = tn | [] -> true)) cands in
      (match ok with
       | [] -> err "E0101" l "no function %s for type %s" m tn
       | u :: _ -> call_sig c l u ~receiver:None args exp)
  | _ -> (
      let tb = infer c b in
      (* a field holding a function is not a method (section 4.7) *)
      let self = repr tb.ty in
      let h = head self in
      let fn_cands =
        List.filter
          (fun u ->
            let sg = Hashtbl.find c.tb.fns u in
            match sg.sparams with
            | (_, _, t, _) :: _ -> head t = h && h <> "_param"
            | [] -> false)
          (lookup_fns c m)
      in
      let generic_cands =
        List.filter
          (fun u ->
            let sg = Hashtbl.find c.tb.fns u in
            match sg.sparams with
            | (_, _, t, _) :: _ -> (match repr t with TParam _ -> true | _ -> false)
            | [] -> false)
          (lookup_fns c m)
      in
      let trait_cands =
        Hashtbl.fold
          (fun tn tr acc ->
            match List.assoc_opt m tr.trmethods_ with
            | Some sg ->
                let has =
                  match self with
                  | TParam p -> (
                      match List.assoc_opt p c.tparams with
                      | Some bs -> List.exists (fun (t, _) -> t = tn) bs
                      | None -> false)
                  | _ ->
                      List.exists (fun im -> im.itrait_ = tn && (let s = ref [] in match_ty (List.map fst im.itparams) s im.ifor_ self)) c.tb.impls
                      || (List.mem tn (prim_traits self))
                in
                if has then (tn, sg) :: acc else acc
            | None -> acc)
          c.tb.traits []
      in
      let recv_mode u = match (Hashtbl.find c.tb.fns u).sparams with (m, _, _, _) :: _ -> m | [] -> MBorrow in
      let check_recv mode =
        if mode = MMut && not (mutable_place c b) then
          err "E0303" b.loc "the receiver of this call is passed as mut and must be a mutable place"
      in
      match (fn_cands, trait_cands) with
      | [ u ], _ -> check_recv (recv_mode u); call_sig c l u ~receiver:(Some tb) args exp
      | _ :: _ :: _, _ -> err "E0105" l "'%s' matches more than one function" m
      | [], [ (tn, sg) ] -> trait_call c l tn [] m sg self (Some tb) args exp
      | [], _ :: _ :: _ -> err "E0105" l "method '%s' matches more than one trait; write Trait.%s(x, ...)" m m
      | [], [] -> (
          match generic_cands with
          | u :: _ -> check_recv (recv_mode u); call_sig c l u ~receiver:(Some tb) args exp
          | [] -> (
              match self with
              | TNamed _ | TTuple _ -> (
                  (* (x.f)(args) is required for a function-valued field *)
                  match (try Some (field_of c l tb m) with Error _ -> None) with
                  | Some { ty = TFn _; _ } -> err "E0201" l "'%s' is a field holding a function; call it as (x.%s)(...)" m m
                  | _ -> err "E0101" l "%s has no method '%s'" (show_ty self) m)
              | TVar _ -> err "E0201" l "the type of this value must be known before '.%s(...)'; add an annotation" m
              | _ -> err "E0101" l "%s has no method '%s'" (show_ty self) m)))

and trait_call c l tn trargs m (sg : fsig) self (receiver : texpr option) args exp : texpr =
  let tr = Hashtbl.find c.tb.traits tn in
  let ta = List.map (fun _ -> fresh ()) tr.trparams in
  let s = ("Self", self) :: List.combine tr.trparams ta in
  let ps = List.map (fun (md, n, t, d) -> (md, n, subst s t, d)) sg.sparams in
  let ret = subst s sg.sret in
  let targs, _ = check_args c l ~receiver ps args in
  (* pick the impl's trait arguments when exactly one impl fits *)
  (match repr self with
   | TParam p -> (
       match List.assoc_opt p c.tparams with
       | Some bs -> (match List.assoc_opt tn bs with Some bta -> List.iter2 (fun a b -> unify_at l a b) ta bta | None -> ())
       | None -> ())
   | _ -> ());
  c.obligations <- (self, tn, ta, l) :: c.obligations;
  let convs = add_eff c l { sg.seff with errs = List.map (subst s) sg.seff.errs } in
  mk (XCall (CTrait (tn, ta, m, self), targs, convs)) ret l

and infer_bracket c l (b : Syntax.expr) (args : Syntax.barg list) exp : texpr =
  (* explicit type arguments: parse[Int](text) are handled by the call; here: indexing *)
  match args with
  | [ BExpr { d = Range (lo, hi); _ } ] ->
      let tb = infer c b in
      let tlo = check c lo (TInt IInt) and thi = check c hi (TInt IInt) in
      (match repr tb.ty with
       | TArray _ | TStr -> mk (XSlice (tb, tlo, thi)) tb.ty l
       | t -> err "E0201" l "%s cannot be sliced" (show_ty t))
  | [ BExpr i ] -> (
      match b.d with
      | Name n when lookup c n = None && lookup_fns c n <> [] -> err "E0102" l "explicit type arguments arrive later; '%s' infers them" n
      | _ ->
          let tb = infer c b in
          match repr tb.ty with
          | TArray t ->
              let ti = check c i (TInt IInt) in
              mk (XIndex (tb, ti)) t l
          | TStr -> err "E0201" l "index a Str through chars(s)[i], or slice it with s[a..b]"
          | t -> err "E0201" l "%s cannot be indexed" (show_ty t))
  | [ BType t ] -> err "E0102" (ty_loc t) "type in brackets after a name that is not generic"
  | _ -> err "E0201" l "indexing takes one index"

and infer_lambda c l ps body exp : texpr =
  let expected_fn = match exp with Some (TFn f) -> Some f | _ -> None in
  (match expected_fn with
   | Some f when List.length f.fps <> List.length ps ->
       err "E0203" l "expected a function of %d parameter(s), found %d" (List.length f.fps) (List.length ps)
   | _ -> ());
  let lr = { caps = [] } in
  push_frame c ~lam:lr ();
  let params =
    List.mapi
      (fun i (p : Syntax.param) ->
        let t =
          match p.pty with
          | Some t -> conv_ty c.tb (List.map fst c.tparams) c.self_ty t
          | None -> (
              match expected_fn with
              | Some f -> snd (List.nth f.fps i)
              | None -> err "E0104" p.ploc "parameter '%s' needs a type: nothing says what this function takes" p.pname)
        in
        (match expected_fn with Some f -> unify_at p.ploc (snd (List.nth f.fps i)) t | None -> ());
        let v = new_var p.pname t (p.pmode = MMut) (VParam p.pmode) in
        bind c v p.ploc;
        v)
      ps
  in
  let saved_errs = c.errs and saved_io = c.io and saved_try = c.in_try in
  c.errs <- []; c.io <- false; c.in_try <- 0;
  let saved_decl = c.declared in
  let c' = { c with declared = None } in
  let tbody =
    match body with
    | LExpr e -> (match expected_fn with Some f -> check c' e f.fret | None -> infer c' e)
    | LAssign (pl, op, rhs) ->
        let st = check_assign c' l pl op rhs in
        mk (XBlock ([ st ], unit_e l)) TUnit l
  in
  ignore saved_decl;
  let feff = { errs = c'.errs; io = c'.io; poly = false } in
  c.errs <- saved_errs; c.io <- saved_io; c.in_try <- saved_try;
  c.obligations <- c'.obligations @ c.obligations;
  c.unsolved <- c'.unsolved @ c.unsolved;
  pop_frame c;
  let fty = { fps = List.map2 (fun (p : Syntax.param) v -> (p.pmode, v.vty)) ps params; fret = tbody.ty; feff } in
  incr lambda_counter;
  let lam = { lparams = params; lbody = tbody; lcaps = lr.caps; lfn = fty; lname = Printf.sprintf "lambda%d" !lambda_counter } in
  List.iter (fun v -> if v.vkind = VParam MMut then err "E0320" l "a closure cannot capture the mut parameter '%s'" v.vname) lr.caps;
  if c.tb.final_pass then c.tb.lambdas <- lam :: c.tb.lambdas;
  mk (XLambda lam) (TFn fty) l

and infer_binop c l op a b exp : texpr =
  match op with
  | "and" | "or" ->
      let ta = check c a TBool and tb = check c b TBool in
      mk (XBin ((if op = "and" then And else Or), ta, tb)) TBool l
  | _ ->
      let is_lit (e : Syntax.expr) = match e.d with Lit (LInt _ | LFloat _) | Unop ("-", { d = Lit _; _ }) -> true | _ -> false in
      let ta, tb =
        if is_lit a && not (is_lit b) then
          let tb = infer c b in
          (check c a tb.ty, tb)
        else
          let ta = match exp with Some t when is_numeric t && List.mem op [ "+"; "-"; "*"; "/"; "%"; "+%"; "-%"; "*%" ] -> check c a t | _ -> infer c a in
          let tb =
            match repr ta.ty with
            | TInt _ | TFloat | TF32 | TBool | TChar | TStr | TDur | TBytes when op <> "*" || not (ta.ty = TDur) -> check c b ta.ty
            | TNamed ("Option", _) when (match b.d with Name "None" -> true | _ -> false) -> check c b ta.ty
            | _ -> infer c b
          in
          (ta, tb)
      in
      let t = repr ta.ty in
      let prim = match t with TInt _ | TFloat | TF32 | TBool | TChar | TStr | TDur | TBytes | TUnit -> true | _ -> false in
      let arith = [ ("+", Add); ("-", Sub); ("*", Mul); ("/", Div); ("%", Mod); ("+%", AddW); ("-%", SubW); ("*%", MulW) ] in
      let cmp = [ ("==", Eq); ("!=", Ne); ("<", Lt); ("<=", Le); (">", Gt); (">=", Ge) ] in
      let trait_of = [ ("+", "Add"); ("-", "Sub"); ("*", "Mul"); ("/", "Div") ] in
      if List.mem_assoc op arith then begin
        let bop = List.assoc op arith in
        match t with
        | TInt _ | TFloat | TF32 | TDur | TBytes when prim ->
            unify_at tb.l ta.ty tb.ty;
            if List.mem bop [ AddW; SubW; MulW ] && not (is_int t) then err "E0201" l "'%s' is defined on integers only" op;
            if bop = Mod && not (is_int t) && t <> TFloat && t <> TF32 then err "E0201" l "'%%' needs numbers";
            mk (XBin (bop, ta, tb)) t l
        | TStr when bop = Add ->
            unify_at tb.l TStr tb.ty;
            mk (XBin (Add, ta, tb)) TStr l
        | _ -> (
            match List.assoc_opt op trait_of with
            | Some tr ->
                let trinfo = Hashtbl.find c.tb.traits tr in
                let sg = List.assoc (String.lowercase_ascii tr) trinfo.trmethods_ in
                let ra = fresh () in
                unify_at tb.l ra tb.ty;
                (match t with
                 | TParam _ -> ()
                 | _ ->
                     if not (List.exists (fun im -> im.itrait_ = tr && (let s = ref [] in match_ty (List.map fst im.itparams) s im.ifor_ t)) c.tb.impls) then
                       err "E0204" l "%s does not implement %s, so '%s' is not defined on it" (show_ty t) tr op);
                c.obligations <- (t, tr, [ tb.ty ], l) :: c.obligations;
                let convs = add_eff c l sg.seff in
                mk (XCall (CTrait (tr, [ tb.ty ], String.lowercase_ascii tr, t), [ { amode = MBorrow; a = ta }; { amode = MBorrow; a = tb } ], convs)) t l
            | None -> err "E0204" l "'%s' is not defined on %s" op (show_ty t))
      end else begin
        let bop = List.assoc op cmp in
        unify_at tb.l ta.ty tb.ty;
        let eqop = bop = Eq || bop = Ne in
        if prim && (eqop || t <> TUnit) then mk (XBin (bop, ta, tb)) TBool l
        else if eqop then begin
          c.obligations <- (t, "Eq", [], l) :: c.obligations;
          let call = mk (XCall (CTrait ("Eq", [], "eq", t), [ { amode = MBorrow; a = ta }; { amode = MBorrow; a = tb } ], [])) TBool l in
          if bop = Eq then call else mk (XNot call) TBool l
        end else begin
          c.obligations <- (t, "Ord", [], l) :: c.obligations;
          let call = mk (XCall (CTrait ("Ord", [], "cmp", t), [ { amode = MBorrow; a = ta }; { amode = MBorrow; a = tb } ], [])) (TInt IInt) l in
          mk (XBin (bop, call, mk (XLit (LInt "0")) (TInt IInt) l)) TBool l
        end
      end

(* ---------- places and assignment ---------- *)

and place_of c (e : Syntax.expr) : place =
  let rec go (e : Syntax.expr) : place =
    match e.d with
    | Name n -> (
        match lookup c n with
        | Some v ->
            check_not_lent c e.loc v;
            if not (v.vmut || v.vkind = VParam MMut) then
              err "E0103" e.loc "'%s' is not mutable; declare it with var" n;
            { root = v; path = []; pty = v.vty }
        | None -> unknown_name c e.loc n)
    | Field (b, f) -> (
        let p = go b in
        match repr p.pty with
        | TNamed (tn, args) -> (
            let d = Hashtbl.find c.tb.decls tn in
            match d.dbody with
            | DStruct fs ->
                let s = List.combine d.dparams args in
                let rec find i = function
                  | [] -> err "E0201" e.loc "%s has no field '%s'" (show_ty p.pty) f
                  | fi :: rest -> if fi.fname_ = f then { p with path = p.path @ [ PField (i, f) ]; pty = subst s fi.fty } else find (i + 1) rest
                in
                find 0 fs
            | _ -> err "E0103" e.loc "fields of a data type cannot be assigned; build a new value")
        | TTuple ts -> (
            match int_of_string_opt f with
            | Some i when i < List.length ts -> { p with path = p.path @ [ PTupleIx i ]; pty = List.nth ts i }
            | _ -> err "E0201" e.loc "no field %s" f)
        | t -> err "E0201" e.loc "%s has no field '%s'" (show_ty t) f)
    | Bracket (b, [ BExpr i ]) when (match i.d with Range _ -> false | _ -> true) -> (
        let p = go b in
        match repr p.pty with
        | TArray t -> { p with path = p.path @ [ PIndex (check c i (TInt IInt)) ]; pty = t }
        | t -> err "E0201" e.loc "%s cannot be indexed" (show_ty t))
    | _ -> err "E0103" e.loc "the left side of an assignment must be a variable, field or element"
  in
  go e

and place_expr (p : place) l : texpr =
  List.fold_left
    (fun (acc : texpr) pr ->
      let ty_after =
        match (pr, repr acc.ty) with
        | _ -> acc.ty
      in
      ignore ty_after;
      match pr with
      | PField (i, f) -> { e = XField (acc, i, f); ty = TUnit; l }
      | PTupleIx i -> { e = XTupleGet (acc, i); ty = TUnit; l }
      | PIndex ix -> { e = XIndex (acc, ix); ty = TUnit; l })
    (mk (XVar p.root) p.root.vty l) p.path
  |> fun te -> { te with ty = p.pty }

and fix_place_types c (te : texpr) : texpr =
  (* recompute intermediate types of a place expression *)
  match te.e with
  | XVar _ -> te
  | XField (b, i, f) -> let b = fix_place_types c b in { (field_of c te.l b f) with l = te.l }
  | XTupleGet (b, i) -> let b = fix_place_types c b in (match repr b.ty with TTuple ts -> { te with e = XTupleGet (b, i); ty = List.nth ts i } | _ -> te)
  | XIndex (b, i) -> let b = fix_place_types c b in (match repr b.ty with TArray t -> { te with e = XIndex (b, i); ty = t } | _ -> te)
  | _ -> te

and check_assign c l (lhs : Syntax.expr) op (rhs : Syntax.expr) : tstmt =
  if not (is_place lhs) then err "E0103" lhs.loc "the left side of an assignment must be a variable, field or element";
  let p = place_of c lhs in
  if op = "=" then begin
    let rhs = check c rhs p.pty in
    (* assigning the whole variable gives it a value again *)
    if p.path = [] then c.moved <- List.filter (fun (id, _) -> id <> p.root.vid) c.moved
    else if List.mem_assoc p.root.vid c.moved then
      err "E0302" l "'%s' is used after it was moved by 'take'" p.root.vname;
    { st = SAssign (p, rhs); sl = l }
  end
  else begin
    let bop = String.sub op 0 1 in
    let cur = fix_place_types c (place_expr p l) in
    (* reuse binop typing on a synthetic tree whose left side is already typed *)
    let tr = infer_binop_typed c l bop cur rhs in
    { st = SAssign (p, tr); sl = l }
  end

and infer_binop_typed c l op (ta : texpr) (b : Syntax.expr) : texpr =
  let t = repr ta.ty in
  match t with
  | TInt _ | TFloat | TF32 | TDur | TBytes | TStr ->
      let tb = check c b ta.ty in
      let bop = match op with "+" -> Add | "-" -> Sub | "*" -> Mul | "/" -> Div | "%" -> Mod | _ -> assert false in
      if t = TStr && bop <> Add then err "E0201" l "'%s=' is not defined on Str" op;
      mk (XBin (bop, ta, tb)) t l
  | _ -> (
      let tr = match op with "+" -> "Add" | "-" -> "Sub" | "*" -> "Mul" | "/" -> "Div" | _ -> err "E0204" l "'%s=' is not defined on %s" op (show_ty t) in
      let tb = infer c b in
      if (match t with TParam _ -> false | _ -> true)
         && not (List.exists (fun im -> im.itrait_ = tr && (let s = ref [] in match_ty (List.map fst im.itparams) s im.ifor_ t)) c.tb.impls) then
        err "E0204" l "%s does not implement %s" (show_ty t) tr;
      c.obligations <- (t, tr, [ tb.ty ], l) :: c.obligations;
      mk (XCall (CTrait (tr, [ tb.ty ], String.lowercase_ascii tr, t), [ { amode = MBorrow; a = ta }; { amode = MBorrow; a = tb } ], [])) t l)

(* ---------- patterns ---------- *)

and check_pat c (p : Syntax.pattern) (t : ty) (refutable : bool) : tpat =
  let l = p.ploc_ in
  match p.p with
  | PWild -> TPWild
  | PVar n ->
      let v = new_var n t false VLocal in
      bind c v l;
      TPVar v
  | PLit lit | PNeg lit ->
      let lit = match (p.p, lit) with
        | PNeg _, LInt s -> LInt ("-" ^ s)
        | PNeg _, LFloat f -> LFloat (-. f)
        | _ -> lit in
      (match (lit, repr t) with
       | LInt s, TInt k -> int_fits k s l
       | LInt s, _ -> int_fits IInt s l
       | _ -> ());
      let lt = match lit with
        | LInt _ -> (match repr t with TInt _ as k -> k | _ -> TInt IInt)
        | LFloat _ -> (match repr t with TF32 -> TF32 | _ -> TFloat)
        | LStr _ -> TStr | LChar _ -> TChar | LBool _ -> TBool | LUnit -> TUnit | LDur _ -> TDur in
      unify_at l t lt;
      TPLit (lit, lt)
  | PTuple ps -> (
      match repr t with
      | TTuple ts when List.length ts = List.length ps -> TPTuple (List.map2 (fun p t -> check_pat c p t refutable) ps ts)
      | TVar _ ->
          let ts = List.map (fun _ -> fresh ()) ps in
          unify_at l t (TTuple ts);
          TPTuple (List.map2 (fun p t -> check_pat c p t refutable) ps ts)
      | _ -> err "E0201" l "this tuple pattern does not match %s" (show_ty t))
  | PCtor (path, args) -> (
      let name = List.nth path (List.length path - 1) in
      let args = match args with Some a -> a | None -> [] in
      match repr t with
      | TErr members ->
          (* inside Err(...) on a union: a constructor of one member type *)
          let member =
            List.find_opt
              (fun m ->
                match repr m with
                | TNamed (tn, _) -> (
                    tn = name
                    || match Hashtbl.find_opt c.tb.variants name with Some (tn', _) -> tn' = tn | None -> false)
                | _ -> false)
              members
          in
          (match member with
           | Some m -> TPErrType (m, check_pat c p m refutable)
           | None -> err "E0201" l "%s is not one of the error types %s" name (show_ty t))
      | rt -> (
          match Hashtbl.find_opt c.tb.variants name with
          | Some (tn, idx) ->
              let d = Hashtbl.find c.tb.decls tn in
              let targs =
                match rt with
                | TNamed (tn', args) when tn' = tn -> args
                | TVar _ -> let a = List.map (fun _ -> fresh ()) d.dparams in unify_at l t (TNamed (tn, a)); a
                | _ -> err "E0201" l "pattern %s is a %s, but the value is %s" name tn (show_ty t)
              in
              let v = match d.dbody with DData vs -> List.nth vs idx | _ -> assert false in
              let s = List.combine d.dparams targs in
              if List.length args <> List.length v.vfields && not (args = [] && v.vfields = []) then
                err "E0203" l "variant %s has %d field(s), the pattern gives %d" name (List.length v.vfields) (List.length args);
              let sub = List.map2 (fun p fi -> check_pat c p (subst s fi.fty) refutable) args v.vfields in
              TPVariant (tn, targs, idx, sub)
          | None -> (
              match Hashtbl.find_opt c.tb.decls name with
              | Some { dbody = DStruct fs; dparams; _ } ->
                  let targs =
                    match rt with
                    | TNamed (tn', args) when tn' = name -> args
                    | _ -> err "E0201" l "pattern %s does not match %s" name (show_ty t)
                  in
                  let s = List.combine dparams targs in
                  if List.length args <> List.length fs then err "E0203" l "struct %s has %d field(s)" name (List.length fs);
                  TPStruct (name, targs, List.map2 (fun p fi -> check_pat c p (subst s fi.fty) refutable) args fs)
              | _ -> err "E0101" l "unknown variant '%s'" name)))

(* ---------- statements and blocks ---------- *)

(* [want]: Some t when the block's value is used, None when it is a statement. *)
and check_block c (b : Syntax.block) (want : ty option) l : texpr =
  push_frame c ();
  let rec go acc = function
    | [] -> (List.rev acc, unit_e l)
    | [ s ] when want <> None -> (
        match s.s with
        | Expr e -> (List.rev acc, (match want with Some t -> check c e t | None -> infer c e))
        | If _ | Match _ -> (List.rev acc, check_stmt_expr c s want)
        | _ ->
            let ts = check_stmt c s in
            let v = match ts.st with SReturn _ | SBreak | SContinue -> mk (XLit LUnit) TNever s.sloc | SExpr { ty = TNever; _ } -> mk (XLit LUnit) TNever s.sloc | _ -> unit_e s.sloc in
            (List.rev (ts :: acc), v))
    | s :: rest -> go (check_stmt c s :: acc) rest
  in
  let stmts, v = go [] b in
  pop_frame c;
  let v = match want with Some t -> coerce c v t | None -> v in
  mk (XBlock (stmts, v)) v.ty l

and check_stmt_expr c (s : Syntax.stmt) (want : ty option) : texpr =
  let l = s.sloc in
  match s.s with
  | If (branches, els) ->
      let before = c.moved in
      let after = ref before in
      let branch f = c.moved <- before; let r = f () in after := union_moved !after c.moved; r in
      let rec build = function
        | [] -> (match els with Some b -> branch (fun () -> check_block c b want l) | None ->
            (match want with Some t when (match repr t with TUnit | TVar _ -> false | _ -> true) ->
               err "E0201" l "this if has no else branch, so it has no value of type %s" (show_ty t) | _ -> ());
            unit_e l)
        | (cnd, blk) :: rest ->
            c.moved <- before;
            let tc = check c cnd TBool in
            let before_branch = c.moved in
            let tb = c.moved <- before_branch; let r = check_block c blk want l in after := union_moved !after c.moved; r in
            let te = build rest in
            let ty = match want with Some t -> t | None -> TUnit in
            mk (XIf (tc, tb, te)) ty l
      in
      let r = build branches in
      c.moved <- !after;
      r
  | Match (scrut, arms) ->
      let ts = infer c scrut in
      let before = c.moved in
      let after = ref before in
      let tarms =
        List.map
          (fun (a : Syntax.arm) ->
            c.moved <- before;
            push_frame c ();
            let p = check_pat c a.apat ts.ty true in
            let g = Option.map (fun g -> check c g TBool) a.aguard in
            let body = check_block c a.abody want a.arm_loc in
            pop_frame c;
            after := union_moved !after c.moved;
            { pat = p; guard = g; body })
          arms
      in
      c.moved <- !after;
      Exhaust.check c.tb.decls (zonk ts.ty) (List.map (fun a -> (a.pat, a.guard <> None)) tarms) l
        (List.map (fun (a : Syntax.arm) -> a.arm_loc) arms);
      let ty = match want with Some t -> t | None -> TUnit in
      mk (XMatch (ts, tarms)) ty l
  | _ -> assert false

and check_stmt c (s : Syntax.stmt) : tstmt =
  let l = s.sloc in
  let mks st = { st; sl = l } in
  match s.s with
  | Let (p, t, e) ->
      let te =
        match t with
        | Some t -> check c e (conv_ty c.tb (List.map fst c.tparams) c.self_ty t)
        | None -> infer c e
      in
      let tp = check_pat c p te.ty false in
      (match (tp, te.e) with
       | TPVar v, XLambda lam -> Hashtbl.replace c.closure_caps v.vid lam.lcaps
       | TPVar v, XVar w when Hashtbl.mem c.closure_caps w.vid -> Hashtbl.replace c.closure_caps v.vid (Hashtbl.find c.closure_caps w.vid)
       | _ -> ());
      (match p.p with
       | PVar _ | PWild | PTuple _ -> ()
       | _ -> Exhaust.check c.tb.decls (zonk te.ty) [ (tp, false) ] l [ l ]);
      mks (SLet (tp, te))
  | Var (_, n, t, e) ->
      let te =
        match t with
        | Some t -> check c e (conv_ty c.tb (List.map fst c.tparams) c.self_ty t)
        | None -> infer c e
      in
      let v = new_var n te.ty true VLocal in
      bind c v l;
      mks (SVar (v, te))
  | Assign (lhs, op, rhs) -> check_assign c l lhs op rhs
  | Return e ->
      let te = match e with Some e -> check c e c.ret | None -> unify_at l c.ret TUnit; unit_e l in
      mks (SReturn te)
  | Break -> if c.loops = 0 then err "E0100" l "break outside a loop"; mks SBreak
  | Continue -> if c.loops = 0 then err "E0100" l "continue outside a loop"; mks SContinue
  | Check e -> mks (SCheck (check c e TBool))
  | Assert e -> mks (SAssert (check c e TBool, ""))
  | AssertFails (t, e) ->
      let et = conv_ty c.tb (List.map fst c.tparams) c.self_ty t in
      let saved = c.errs in
      c.errs <- [];
      c.in_try <- c.in_try + 1;
      let te = infer c e in
      c.in_try <- c.in_try - 1;
      c.errs <- saved;
      mks (SAssertFails (et, te))
  | AssertSnapshot _ -> err "E0100" l "snapshot tests arrive in milestone 2"
  | Expr e -> mks (SExpr (infer c e))
  | If _ | Match _ -> mks (SExpr (check_stmt_expr c s None))
  | For (true, _, _, _, _) -> err "E0700" l "par for arrives in milestone 6"
  | For (false, p, m, it, body) ->
      if m = MMut && not (mutable_place c it) then err "E0303" it.loc "'for x in mut xs' needs a mutable place";
      let src, elt = check_iter c it m in
      push_frame c ();
      let tp =
        match (m, p.p) with
        | MMut, PVar n -> let v = new_var n elt true (VParam MMut) in bind c v p.ploc_; TPVar v
        | MMut, _ -> err "E0303" p.ploc_ "'for ... in mut' binds a single name"
        | _ -> check_pat c p elt false
      in
      c.loops <- c.loops + 1;
      let before = c.moved in
      (* each element is lent as a mut place: the body must not touch the array itself *)
      let rec root (e : Syntax.expr) = match e.d with Name n -> lookup c n | Field (b, _) | Bracket (b, _) -> root b | _ -> None in
      let saved_lent = c.lent in
      (if m = MMut then match root it with Some v -> c.lent <- (v.vid, it.loc) :: c.lent | None -> ());
      let tb = check_block c body None l in
      c.lent <- saved_lent;
      c.loops <- c.loops - 1;
      pop_frame c;
      (* checked after the loop variable's frame is gone: it is fresh on every pass *)
      loop_moves c before;
      mks (SFor (tp, src, tb))
  | While (cnd, body) ->
      let tc = check c cnd TBool in
      c.loops <- c.loops + 1;
      let before = c.moved in
      let tb = check_block c body None l in
      loop_moves c before;
      c.loops <- c.loops - 1;
      mks (SWhile (tc, tb))
  | LocalFn fd ->
      (* a local fn is a closure bound to an immutable name (section 2.2) *)
      let ps = fd.fparams in
      let ret = match fd.fret with Some t -> conv_ty c.tb (List.map fst c.tparams) c.self_ty t | None -> TUnit in
      let lr = { caps = [] } in
      push_frame c ~lam:lr ();
      let params = List.map (fun (p : Syntax.param) ->
          let t = conv_ty c.tb (List.map fst c.tparams) c.self_ty (Option.get p.pty) in
          let v = new_var p.pname t (p.pmode = MMut) (VParam p.pmode) in
          bind c v p.ploc; v) ps in
      let c' = { c with declared = None; errs = []; io = false; in_try = 0; loops = 0; ret } in
      let body = check_block c' (Option.get fd.fbody) (Some ret) l in
      pop_frame c;
      c.obligations <- c'.obligations @ c.obligations;
      c.unsolved <- c'.unsolved @ c.unsolved;
      let fty = { fps = List.map2 (fun (p : Syntax.param) v -> (p.pmode, v.vty)) ps params; fret = ret; feff = { errs = c'.errs; io = c'.io; poly = false } } in
      incr lambda_counter;
      let lam = { lparams = params; lbody = body; lcaps = lr.caps; lfn = fty; lname = Printf.sprintf "%s_%d" fd.fname !lambda_counter } in
      if c.tb.final_pass then c.tb.lambdas <- lam :: c.tb.lambdas;
      let v = new_var fd.fname (TFn fty) false VLocal in
      bind c v l;
      Hashtbl.replace c.closure_caps v.vid lam.lcaps;
      mks (SLocalFn (v, lam))
  | Lend _ -> err "E0320" l "lend functions (section 4.6) are not implemented yet"
  | Resume _ -> err "E0100" l "resume arrives with handlers in milestone 4"


(* ---------- zonking the typed tree ---------- *)

let rec zonk_e (te : texpr) : texpr =
  let z = zonk_e in
  let e =
    match te.e with
    | XLit _ | XNone -> te.e
    | XVar v -> v.vty <- zonk v.vty; te.e
    | XFStr ps -> XFStr (List.map z ps)
    | XFnRef (n, ts) -> XFnRef (n, List.map zonk ts)
    | XCall (cl, args, convs) ->
        let cl = match cl with
          | CFn (n, ts) -> CFn (n, List.map zonk ts)
          | CBuiltin (n, ts) -> CBuiltin (n, List.map zonk ts)
          | CTrait (t, ta, m, s) -> CTrait (t, List.map zonk ta, m, zonk s)
          | CClosure f -> CClosure (z f) in
        XCall (cl, List.map (fun a -> { a with a = z a.a }) args,
               List.map (fun cv -> { cv with cfrom = zonk cv.cfrom; cto = zonk cv.cto }) convs)
    | XField (b, i, f) -> XField (z b, i, f)
    | XTupleGet (b, i) -> XTupleGet (z b, i)
    | XIndex (a, b) -> XIndex (z a, z b)
    | XSlice (a, b, c) -> XSlice (z a, z b, z c)
    | XTuple es -> XTuple (List.map z es)
    | XArray es -> XArray (List.map z es)
    | XStruct (n, ts, es) -> XStruct (n, List.map zonk ts, List.map z es)
    | XVariant (n, ts, i, es) -> XVariant (n, List.map zonk ts, i, List.map z es)
    | XIf (a, b, c) -> XIf (z a, z b, z c)
    | XBlock (ss, v) -> XBlock (List.map zonk_s ss, z v)
    | XMatch (s, arms) -> XMatch (z s, List.map (fun a -> { pat = zonk_p a.pat; guard = Option.map z a.guard; body = z a.body }) arms)
    | XLambda lam -> XLambda (zonk_lam lam)
    | XBin (o, a, b) -> XBin (o, z a, z b)
    | XNeg a -> XNeg (z a)
    | XNot a -> XNot (z a)
    | XTry a -> XTry (z a)
    | XConv a -> XConv (z a)
    | XFail a -> XFail (z a)
    | XComp (b, cs) -> XComp (z b, List.map (fun cp -> { cvar = zonk_p cp.cvar; csrc = zonk_it cp.csrc; ccond = Option.map z cp.ccond }) cs)
  in
  { te with e; ty = zonk te.ty }

and zonk_lam lam =
  List.iter (fun v -> v.vty <- zonk v.vty) lam.lparams;
  List.iter (fun v -> v.vty <- zonk v.vty) lam.lcaps;
  { lam with lbody = zonk_e lam.lbody; lfn = zonk_fn lam.lfn }

and zonk_it = function
  | IRange (a, b) -> IRange (zonk_e a, zonk_e b)
  | IArray (a, m) -> IArray (zonk_e a, m)

and zonk_p = function
  | TPVar v -> v.vty <- zonk v.vty; TPVar v
  | TPLit (l, t) -> TPLit (l, zonk t)
  | TPVariant (n, ts, i, ps) -> TPVariant (n, List.map zonk ts, i, List.map zonk_p ps)
  | TPStruct (n, ts, ps) -> TPStruct (n, List.map zonk ts, List.map zonk_p ps)
  | TPTuple ps -> TPTuple (List.map zonk_p ps)
  | TPErrType (t, p) -> TPErrType (zonk t, zonk_p p)
  | TPWild -> TPWild

and zonk_s (s : tstmt) : tstmt =
  let st =
    match s.st with
    | SLet (p, e) -> SLet (zonk_p p, zonk_e e)
    | SVar (v, e) -> v.vty <- zonk v.vty; SVar (v, zonk_e e)
    | SAssign (p, e) ->
        p.root.vty <- zonk p.root.vty;
        SAssign ({ p with path = List.map (function PIndex i -> PIndex (zonk_e i) | x -> x) p.path; pty = zonk p.pty }, zonk_e e)
    | SExpr e -> SExpr (zonk_e e)
    | SReturn e -> SReturn (zonk_e e)
    | SBreak | SContinue -> s.st
    | SWhile (c, b) -> SWhile (zonk_e c, zonk_e b)
    | SFor (p, it, b) -> SFor (zonk_p p, zonk_it it, zonk_e b)
    | SAssert (e, src) -> SAssert (zonk_e e, src)
    | SAssertFails (t, e) -> SAssertFails (zonk t, zonk_e e)
    | SCheck e -> SCheck (zonk_e e)
    | SLocalFn (v, lam) -> v.vty <- zonk v.vty; SLocalFn (v, zonk_lam lam)
  in
  { s with st }

(* Every type in the tree must be known after checking (E0210). *)
let rec has_tvar t =
  match repr t with
  | TVar _ -> true
  | TArray t -> has_tvar t
  | TTuple ts | TNamed (_, ts) | TErr ts -> List.exists has_tvar ts
  | TFn f -> List.exists (fun (_, t) -> has_tvar t) f.fps || has_tvar f.fret
  | _ -> false

(* ---------- declarations ---------- *)

let module_name path =
  let b = Filename.remove_extension (Filename.basename path) in
  String.map (fun ch -> if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') then ch else '_') b

let tparams_of tb (gs : gparam list) self =
  let names = List.map (fun g -> g.gname) gs in
  List.map
    (fun g ->
      ( g.gname,
        List.map
          (fun b ->
            match b with
            | TyPath ([ tr ], args, l) ->
                if not (Hashtbl.mem tb.traits tr) then err "E0101" l "unknown trait '%s'" tr;
                let info = Hashtbl.find tb.traits tr in
                let args = List.map (conv_ty tb names self) args in
                (* a bound such as T: Add means Add[T] *)
                let args = if args = [] then List.map (fun _ -> TParam g.gname) info.trparams else args in
                (tr, args)
            | t -> err "E0101" (ty_loc t) "a bound must name a trait")
          g.gbounds ))
    gs

let make_sig tb ~modname ~uname (fd : Syntax.fn_def) (extra_tps : (string * (string * ty list) list) list) self : fsig =
  let own = tparams_of tb fd.fgenerics self in
  let tps = extra_tps @ own in
  let names = List.map fst tps in
  let params =
    List.map
      (fun (p : Syntax.param) ->
        match p.pty with
        | Some t -> (p.pmode, p.pname, conv_ty tb names self t, p.pdefault)
        | None -> err "E0104" p.ploc "parameter '%s' needs a type" p.pname)
      fd.fparams
  in
  let ret = match fd.fret with Some t -> conv_ty tb names self t | None -> TUnit in
  let declared, eff =
    match fd.feffects with
    | Some es -> (true, conv_effects tb names self es)
    | None -> (fd.fexport, no_eff)
  in
  if fd.fret_lend <> None then err "E0320" fd.floc "lend functions (section 4.6) are not implemented yet";
  { sname = uname; sdisplay = fd.fname; stparams = tps; sparams = params; sret = ret; seff = eff;
    sdeclared = declared; sexport = fd.fexport; sloc = fd.floc; smodule = modname }

let register_fn tb (sg : fsig) =
  Hashtbl.replace tb.fns sg.sname sg;
  let prev = try Hashtbl.find tb.by_name sg.sdisplay with Not_found -> [] in
  Hashtbl.replace tb.by_name sg.sdisplay (prev @ [ sg.sname ])

let unique_name tb modname name =
  let base = modname ^ "__" ^ name in
  if not (Hashtbl.mem tb.fns base) then base
  else
    let rec go i = let n = Printf.sprintf "%s_%d" base i in if Hashtbl.mem tb.fns n then go (i + 1) else n in
    go 2

let declare_types tb modname (items : item list) =
  (* first the names, so that types can refer to each other *)
  List.iter
    (function
      | IType td ->
          if Hashtbl.mem tb.decls td.tname || List.mem_assoc td.tname prim_names then
            err "E0101" td.tloc "type '%s' is already defined" td.tname;
          if td.tresource then err "E0400" td.tloc "resource types arrive in milestone 4";
          Hashtbl.replace tb.decls td.tname
            { dname = td.tname; dparams = List.map (fun g -> g.gname) td.tgenerics; dbody = DStruct [];
              dexport = td.texport; dopen = td.topen; dloc = td.tloc; dmodule = modname }
      | _ -> ())
    items;
  List.iter
    (function
      | IType td ->
          let d = Hashtbl.find tb.decls td.tname in
          let ps = d.dparams in
          let conv_fields fs =
            List.mapi (fun i f -> { fname_ = (match f.fdname with Some n -> n | None -> string_of_int i); fty = conv_ty tb ps None f.fdty }) fs
          in
          let body =
            match td.tbody with
            | BStruct fs ->
                Hashtbl.replace defaults_table td.tname (List.map (fun f -> f.fddefault) fs);
                DStruct (conv_fields fs)
            | BData [ { vname; vfields = None; _ } ] when (Hashtbl.mem tb.decls vname || List.mem_assoc vname prim_names) && vname <> td.tname ->
                DAlias (conv_ty tb ps None (TyPath ([ vname ], [], td.tloc)))
            | BData vs ->
                DData
                  (List.mapi
                     (fun i (v : Syntax.variant) ->
                       if Hashtbl.mem tb.variants v.vname then err "E0101" v.vloc "variant '%s' is already defined" v.vname;
                       Hashtbl.replace tb.variants v.vname (td.tname, i);
                       let fs = match v.vfields with Some fs -> fs | None -> [] in
                       Hashtbl.replace defaults_table (td.tname ^ "." ^ v.vname) (List.map (fun f -> f.fddefault) fs);
                       { vname_ = v.vname; vfields = conv_fields fs; vnamed = List.for_all (fun f -> f.fdname <> None) fs; vindex = i })
                     vs)
            | BAlias t -> DAlias (conv_ty tb ps None t)
            | BNone -> err "E0100" td.tloc "type '%s' needs a definition" td.tname
          in
          d.dbody <- body
      | _ -> ())
    items

let declare_items tb modname (items : item list) =
  (* traits *)
  List.iter
    (function
      | ITrait tr ->
          let ps = List.map (fun g -> g.gname) tr.trgenerics in
          let info = { trname_ = tr.trname; trparams = ps; trmethods_ = [] } in
          Hashtbl.replace tb.traits tr.trname info
      | _ -> ())
    items;
  List.iter
    (function
      | ITrait tr ->
          let info = Hashtbl.find tb.traits tr.trname in
          let ms =
            List.map
              (fun (fd : Syntax.fn_def) ->
                let sg = make_sig tb ~modname ~uname:(tr.trname ^ "." ^ fd.fname) fd (List.map (fun p -> (p, [])) info.trparams) (Some (TParam "Self")) in
                (fd.fname, { sg with sdeclared = true }))
              tr.trmethods
          in
          Hashtbl.replace tb.traits tr.trname { info with trmethods_ = ms }
      | _ -> ())
    items;
  (* functions *)
  List.iter
    (function
      | IFn fd ->
          let uname =
            if fd.fbody = None then
              builtin_prefix ^ fd.fname ^ "@"
              ^ (match fd.fparams with
                 | { pty = Some (TyPath ([ h ], _, _)); _ } :: _ -> h
                 | _ -> "")
            else unique_name tb modname fd.fname
          in
          let sg = make_sig tb ~modname ~uname fd [] None in
          let sg = if fd.fbody = None then { sg with sdeclared = true } else sg in
          register_fn tb sg;
          if fd.fbody <> None then Hashtbl.replace tb.bodies uname (fd, [])
      | IConst (n, _, t, e, l) -> Hashtbl.replace tb.consts n (e, Option.map (conv_ty tb [] None) t, l)
      | _ -> ())
    items;
  (* impls *)
  List.iter
    (function
      | IImpl im ->
          let trn = String.concat "." im.itrait in
          let info =
            match Hashtbl.find_opt tb.traits trn with
            | Some i -> i
            | None -> err "E0101" im.iloc "unknown trait '%s'" trn
          in
          let tps0 = List.map (fun g -> g.gname) im.igenerics in
          let fty = conv_ty tb tps0 None im.ifor in
          let tps = tparams_of tb im.igenerics (Some fty) in
          let targs = List.map (conv_ty tb tps0 (Some fty)) im.itargs in
          let targs = if targs = [] then List.map (fun _ -> fty) info.trparams else targs in
          if List.length targs <> List.length info.trparams then
            err "E0201" im.iloc "trait %s takes %d type argument(s)" trn (List.length info.trparams);
          let methods =
            List.map
              (fun (fd : Syntax.fn_def) ->
                if not (List.mem_assoc fd.fname info.trmethods_) then
                  err "E0101" fd.floc "trait %s has no method '%s'" trn fd.fname;
                let uname = unique_name tb modname (trn ^ "_" ^ head fty ^ "_" ^ fd.fname) in
                let sg = make_sig tb ~modname ~uname fd tps (Some fty) in
                (* the impl's effects may be fewer than the trait's, never more *)
                let tsig = List.assoc fd.fname info.trmethods_ in
                let sg = { sg with seff = (if fd.feffects = None then tsig.seff else sg.seff); sdeclared = true; sdisplay = "" } in
                Hashtbl.replace tb.fns uname sg;
                Hashtbl.replace tb.bodies uname (fd, [ ("Self", fty) ]);
                (fd.fname, uname))
              im.imethods
          in
          List.iter
            (fun (mn, _) ->
              if not (List.mem_assoc mn methods) && trn <> "Copy" then
                err "E0204" im.iloc "impl of %s for %s is missing method '%s'" trn (show_ty fty) mn)
            info.trmethods_;
          tb.impls <- tb.impls @ [ { itparams = tps; itrait_ = trn; itargs_ = targs; ifor_ = fty; imethods_ = methods; iloc_ = im.iloc } ]
      | _ -> ())
    items

(* ---------- checking bodies ---------- *)

let new_ctx tb (sg : fsig) self : fctx =
  { tb; frames = [ { vars = []; lam = None } ]; tparams = sg.stparams; ret = sg.sret; errs = []; io = false;
    in_try = 0; loops = 0;
    declared = (if sg.sdeclared && (sg.seff.errs <> [] || sg.sexport) then Some sg.seff.errs else None);
    obligations = []; unsolved = []; moved = []; lent = []; closure_caps = Hashtbl.create 8; fname = sg.sdisplay; self_ty = self }

let finish_ctx c l =
  List.iter
    (fun (t, tr, ta, l) ->
      let t = zonk t in
      if has_tvar t then ()
      else if find_impl c.tb ~bounds:c.tparams tr (List.map zonk ta) t = None then
        err "E0204" l "%s does not implement %s" (show_ty t) tr)
    c.obligations;
  List.iter (fun (t, l) -> if has_tvar t then err "E0210" l "the element type of this empty literal is never settled; add an annotation") c.unsolved

let check_fn tb uname : tfn =
  let sg = Hashtbl.find tb.fns uname in
  let fd, selfb = Hashtbl.find tb.bodies uname in
  let self = List.assoc_opt "Self" selfb in
  let c = new_ctx tb sg self in
  let params =
    List.map
      (fun (m, n, t, _) ->
        let v = new_var n t (m = MMut) (VParam m) in
        bind c v sg.sloc;
        v)
      sg.sparams
  in
  let body = check_block c (Option.get fd.fbody) (Some sg.sret) sg.sloc in
  finish_ctx c sg.sloc;
  let body = zonk_e body in
  (* effects: inferred for private functions, checked for exported ones *)
  if sg.sdeclared && sg.sdisplay <> "" then begin
    if c.io && not sg.seff.io && tb.final_pass then
      err "E0503" sg.sloc "'%s' performs io, which its signature does not list; add '! io'" sg.sdisplay;
    if sg.seff.errs = [] && sg.sexport then
      List.iter (fun e -> if tb.final_pass then err "E0501" sg.sloc "'%s' can fail with %s, which it does not list" sg.sdisplay (show_ty e)) c.errs
  end;
  if not sg.sdeclared then sg.seff <- { sg.seff with errs = c.errs; io = c.io }
  else if sg.seff.errs = [] && not sg.sexport then sg.seff <- { sg.seff with errs = c.errs; io = sg.seff.io || c.io };
  { fsig = sg; fparams = params; fbody = body }

let check_const tb n =
  let e, t, _ = Hashtbl.find tb.consts n in
  let sg = { sname = "const:" ^ n; sdisplay = n; stparams = []; sparams = []; sret = TUnit; seff = no_eff; sdeclared = false;
             sexport = false; sloc = e.loc; smodule = "" } in
  let c = new_ctx tb sg None in
  let te = match t with Some t -> check c e t | None -> infer c e in
  finish_ctx c e.loc;
  let te = zonk_e te in
  if c.io || c.errs <> [] then err "E0503" e.loc "a constant cannot perform effects or fail";
  Hashtbl.replace tb.typed_consts n te

let new_tables () =
  { decls = Hashtbl.create 64; variants = Hashtbl.create 64; fns = Hashtbl.create 64; by_name = Hashtbl.create 64;
    bodies = Hashtbl.create 64; traits = Hashtbl.create 16; impls = []; consts = Hashtbl.create 8;
    typed_consts = Hashtbl.create 8; lambdas = []; final_pass = false; decl_errors = [] }

(* Check a whole program (the prelude plus one module). Effects of private functions are
   inferred by iterating to a fixpoint (section 7.2). *)
let check_program (prelude : Syntax.file) (user : Syntax.file) : tprog =
  let tb = new_tables () in
  let mods = [ ("core", prelude); (module_name user.path, user) ] in
  List.iter (fun (m, f) -> declare_types tb m f.items) mods;
  List.iter (fun (m, f) -> declare_items tb m f.items) mods;
  Hashtbl.iter (fun n _ -> check_const tb n) tb.consts;
  let order = List.concat_map (fun (m, f) -> List.concat_map (function
      | IFn fd when fd.fbody <> None -> List.filter (fun u -> (Hashtbl.find tb.fns u).sloc == fd.floc) (Hashtbl.find tb.by_name fd.fname)
      | IImpl im -> List.concat_map (fun (fd : Syntax.fn_def) ->
          Hashtbl.fold (fun u sg acc -> if sg.sloc == fd.floc then u :: acc else acc) tb.fns []) im.imethods
      | _ -> []) f.items) mods in
  let snapshot () = List.map (fun u -> let sg = Hashtbl.find tb.fns u in (List.map show_ty sg.seff.errs, sg.seff.io)) order in
  let rec iterate n =
    let before = snapshot () in
    List.iter (fun u -> try ignore (check_fn tb u) with Error _ -> ()) order;
    if snapshot () <> before && n < 50 then iterate (n + 1)
  in
  iterate 0;
  tb.final_pass <- true;
  let fns = Hashtbl.create 64 in
  List.iter (fun u -> Hashtbl.replace fns u (check_fn tb u)) order;
  (* tests: each body is a function that may perform io and fail with any error *)
  let tests =
    List.concat_map
      (function
        | ITest t when t.tsrejects = None ->
            let sg = { sname = "test"; sdisplay = t.tsname; stparams = []; sparams = []; sret = TUnit; seff = no_eff;
                       sdeclared = false; sexport = false; sloc = t.tsloc; smodule = module_name user.path } in
            let c = new_ctx tb sg None in
            let body = check_block c t.tsbody (Some TUnit) t.tsloc in
            finish_ctx c t.tsloc;
            [ (t.tsname, zonk_e body, t.tsloc) ]
        | _ -> [])
      user.items
  in
  let main =
    match Hashtbl.find_opt tb.by_name "main" with
    | Some us -> List.find_opt (fun u -> (Hashtbl.find tb.fns u).smodule <> "core") us
    | None -> None
  in
  (match main with
   | Some u ->
       let sg = Hashtbl.find tb.fns u in
       if sg.sparams <> [] then err "E0203" sg.sloc "main takes no parameters";
       (match repr sg.sret with TUnit -> () | _ -> err "E0201" sg.sloc "main returns Unit")
   | None -> ());
  { decls = tb.decls; fns; fn_order = order; traits = tb.traits; impls = tb.impls; tests; main; lambdas = tb.lambdas }

(* Rejection tests (section 20.2): the body must fail to compile with the given code. *)
let rejection_tests (user : Syntax.file) = List.filter_map (function ITest t when t.tsrejects <> None -> Some t | _ -> None) user.items

let tables_of_prog (p : tprog) = p
