(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Types and the typed tree (section 8.1). *)

open Syntax

type ikind = IInt | I8 | I16 | I32 | I64 | U8 | U16 | U32 | U64

type ty =
  | TInt of ikind
  | TFloat
  | TF32
  | TBool
  | TChar
  | TUnit
  | TStr
  | TDur
  | TBytes
  | TNever                        (* type of return, break, fail(...) *)
  | TArray of ty
  | TTuple of ty list
  | TNamed of string * ty list    (* struct or data type, including Option and Result *)
  | TFn of fnty
  | TParam of string
  | TVar of tvar ref
  | TErr of ty list               (* anonymous union of error types (section 5.4) *)
  | TAny of string * ty list      (* trait value: any Figure (section 3.4) *)

and fnty = { fps : (mode * ty) list; fret : ty; feff : eff }

(* Effects of a function type. [poly] marks an effect-polymorphic function parameter
   (section 7.2): what the argument does is added to the caller. *)
and eff = { errs : ty list; io : bool; poly : bool }

and tvar = Unbound of int | Link of ty

let no_eff = { errs = []; io = false; poly = false }
let poly_eff = { errs = []; io = false; poly = true }

let counter = ref 0
let fresh () = incr counter; TVar (ref (Unbound !counter))

(* Speculation: while an attempt is open, every change to a type variable is logged, so
   the attempt can be undone if it fails. *)
let trail : (tvar ref * tvar) list ref = ref []
let speculating = ref 0

let set_var r v =
  if !speculating > 0 then trail := (r, !r) :: !trail;
  r := v

let open_speculation () = incr speculating; !trail

(* the attempt held: its changes stay in the log while an enclosing attempt can still fail *)
let close_speculation () = decr speculating; if !speculating = 0 then trail := []

(* the bindings and compressions logged since [mark], oldest first *)
let trail_since mark =
  let rec go l acc =
    if l == mark then acc else match l with e :: rest -> go rest (e :: acc) | [] -> acc
  in
  go !trail []

let undo_speculation mark =
  let rec go l = if l != mark then match l with (r, old) :: rest -> r := old; go rest | [] -> () in
  go !trail;
  trail := mark

let rec repr t =
  match t with
  | TVar ({ contents = Link t' } as r) ->
      let t'' = repr t' in
      if t'' != t' then set_var r (Link t'');
      t''
  | _ -> t

let ikind_name = function
  | IInt -> "Int" | I8 -> "I8" | I16 -> "I16" | I32 -> "I32" | I64 -> "I64"
  | U8 -> "U8" | U16 -> "U16" | U32 -> "U32" | U64 -> "U64"

let ikind_bits = function
  | I8 | U8 -> 8 | I16 | U16 -> 16 | I32 | U32 -> 32 | IInt | I64 | U64 -> 64

let ikind_signed = function U8 | U16 | U32 | U64 -> false | _ -> true

let rec show_ty t =
  match repr t with
  | TInt k -> ikind_name k
  | TFloat -> "Float"
  | TF32 -> "F32"
  | TBool -> "Bool"
  | TChar -> "Char"
  | TUnit -> "Unit"
  | TStr -> "Str"
  | TDur -> "Duration"
  | TBytes -> "Bytes"
  | TNever -> "Never"
  | TArray t -> "Array[" ^ show_ty t ^ "]"
  | TTuple ts -> "(" ^ String.concat ", " (List.map show_ty ts) ^ ")"
  | TNamed ("Option", [ t ]) -> show_ty t ^ "?"
  | TNamed (n, []) -> n
  | TNamed (n, ts) -> n ^ "[" ^ String.concat ", " (List.map show_ty ts) ^ "]"
  | TFn f ->
      let ps = List.map (fun (m, t) -> (match m with MMut -> "mut " | MTake -> "take " | MBorrow -> "") ^ show_ty t) f.fps in
      let r = match repr f.fret with TUnit -> "" | t -> " -> " ^ show_ty t in
      let e = (if f.feff.io then [ "io" ] else []) @ List.map show_ty f.feff.errs in
      (* a closed, empty effect list is written ! pure (section 7.1) *)
      let e = if e = [] && not f.feff.poly then [ "pure" ] else e in
      "fn(" ^ String.concat ", " ps ^ ")" ^ r ^ (if e = [] then "" else " ! " ^ String.concat ", " e)
  | TParam n -> n
  | TVar { contents = Unbound _ } -> "_"
  | TVar _ -> assert false
  | TErr ts -> String.concat " | " (List.map show_ty ts)
  | TAny (n, []) -> "any " ^ n
  | TAny (n, ts) -> "any " ^ n ^ "[" ^ String.concat ", " (List.map show_ty ts) ^ "]"

(* Fully resolve type variables. *)
let rec zonk t =
  match repr t with
  | TArray t -> TArray (zonk t)
  | TTuple ts -> TTuple (List.map zonk ts)
  | TNamed (n, ts) -> TNamed (n, List.map zonk ts)
  | TAny (n, ts) -> TAny (n, List.map zonk ts)
  | TFn f -> TFn (zonk_fn f)
  | TErr ts -> TErr (List.map zonk ts)
  | t -> t

and zonk_fn f =
  { fps = List.map (fun (m, t) -> (m, zonk t)) f.fps; fret = zonk f.fret;
    feff = { f.feff with errs = List.map zonk f.feff.errs } }

let rec subst (s : (string * ty) list) t =
  match repr t with
  | TParam n -> (try List.assoc n s with Not_found -> t)
  | TArray t -> TArray (subst s t)
  | TTuple ts -> TTuple (List.map (subst s) ts)
  | TNamed (n, ts) -> TNamed (n, List.map (subst s) ts)
  | TAny (n, ts) -> TAny (n, List.map (subst s) ts)
  | TFn f ->
      TFn { fps = List.map (fun (m, t) -> (m, subst s t)) f.fps; fret = subst s f.fret;
            feff = { f.feff with errs = List.map (subst s) f.feff.errs } }
  | TErr ts -> TErr (List.map (subst s) ts)
  | t -> t

let rec occurs r t =
  match repr t with
  | TVar r' -> r == r'
  | TArray t -> occurs r t
  | TTuple ts | TNamed (_, ts) | TErr ts | TAny (_, ts) -> List.exists (occurs r) ts
  | TFn f -> List.exists (fun (_, t) -> occurs r t) f.fps || occurs r f.fret
  | _ -> false

exception Mismatch

(* Structural equality after zonking; used to compare error types. *)
let rec ty_equal a b =
  match (repr a, repr b) with
  | TInt x, TInt y -> x = y
  | TArray x, TArray y -> ty_equal x y
  | TTuple xs, TTuple ys | TNamed (_, xs), TNamed (_, ys) | TErr xs, TErr ys | TAny (_, xs), TAny (_, ys) ->
      (match (repr a, repr b) with
       | TNamed (n, _), TNamed (m, _) | TAny (n, _), TAny (m, _) when n <> m -> false
       | _ -> List.length xs = List.length ys && List.for_all2 ty_equal xs ys)
  | TParam x, TParam y -> x = y
  | TVar r, TVar r' -> r == r'
  | TFn f, TFn g ->
      List.length f.fps = List.length g.fps
      && List.for_all2 (fun (m, x) (n, y) -> m = n && ty_equal x y) f.fps g.fps
      && ty_equal f.fret g.fret
  | x, y -> x = y

(* Equality that also compares the effects of function types. Where a trait argument is
   matched, a function that can fail and one that cannot are different types: treating them
   as one would let a failure reach code that was told it cannot happen. *)
let rec ty_equal_eff a b =
  match (repr a, repr b) with
  | TFn f, TFn g ->
      List.length f.fps = List.length g.fps
      && List.for_all2 (fun (m, x) (n, y) -> m = n && ty_equal_eff x y) f.fps g.fps
      && ty_equal_eff f.fret g.fret
      && f.feff.io = g.feff.io
      && f.feff.poly = g.feff.poly
      && List.for_all (fun x -> List.exists (ty_equal_eff x) g.feff.errs) f.feff.errs
      && List.for_all (fun y -> List.exists (ty_equal_eff y) f.feff.errs) g.feff.errs
  | TArray x, TArray y -> ty_equal_eff x y
  | (TTuple xs, TTuple ys) | (TNamed (_, xs), TNamed (_, ys)) | (TErr xs, TErr ys) | (TAny (_, xs), TAny (_, ys)) ->
      (match (repr a, repr b) with
       | TNamed (n, _), TNamed (m, _) | TAny (n, _), TAny (m, _) when n <> m -> false
       | _ -> List.length xs = List.length ys && List.for_all2 ty_equal_eff xs ys)
  | x, y -> ty_equal x y

let rec unify a b =
  let a = repr a and b = repr b in
  if a == b then ()
  else
    match (a, b) with
    | TNever, _ | _, TNever -> ()
    | TVar r, t | t, TVar r ->
        if occurs r t then raise Mismatch;
        set_var r (Link t)
    | TInt x, TInt y -> if x <> y then raise Mismatch
    | TArray x, TArray y -> unify x y
    | TTuple xs, TTuple ys ->
        if List.length xs <> List.length ys then raise Mismatch;
        List.iter2 unify xs ys
    | TNamed (n, xs), TNamed (m, ys) | TAny (n, xs), TAny (m, ys) ->
        if n <> m || List.length xs <> List.length ys then raise Mismatch;
        List.iter2 unify xs ys
    | TFn f, TFn g ->
        if List.length f.fps <> List.length g.fps then raise Mismatch;
        List.iter2 (fun (m, x) (n, y) -> if m <> n then raise Mismatch; unify x y) f.fps g.fps;
        unify f.fret g.fret
    | TParam x, TParam y -> if x <> y then raise Mismatch
    | TErr xs, TErr ys ->
        if List.length xs <> List.length ys then raise Mismatch;
        List.iter2 unify xs ys
    | x, y -> if x <> y then raise Mismatch

(* Does the type still hold an unresolved type variable? Every type in the tree must be
   known after checking (E0210). *)
let rec has_tvar t =
  match repr t with
  | TVar _ -> true
  | TArray t -> has_tvar t
  | TTuple ts | TNamed (_, ts) | TErr ts | TAny (_, ts) -> List.exists has_tvar ts
  | TFn f -> List.exists (fun (_, t) -> has_tvar t) f.fps || has_tvar f.fret
  | _ -> false

let is_numeric t = match repr t with TInt _ | TFloat | TF32 -> true | _ -> false
let is_int t = match repr t with TInt _ -> true | _ -> false
let opt t = TNamed ("Option", [ t ])

(* ---------- typed tree ---------- *)

type var = {
  vname : string;
  vid : int;
  mutable vty : ty;
  vmut : bool;                    (* declared with var *)
  vkind : vkind;
  mutable vcell : bool;           (* promoted to a shared cell (section 13) *)
  mutable vcaptured : bool;
}

and vkind = VLocal | VParam of mode

let var_counter = ref 0
let new_var name ty mut kind =
  incr var_counter;
  { vname = name; vid = !var_counter; vty = ty; vmut = mut; vkind = kind; vcell = false; vcaptured = false }

type binop =
  | Add | Sub | Mul | Div | Mod | AddW | SubW | MulW
  | Eq | Ne | Lt | Le | Gt | Ge
  | And | Or

type texpr = { e : te; ty : ty; l : loc }

and te =
  | XLit of lit
  | XFStr of texpr list                  (* each part is a Str *)
  | XVar of var
  | XFnRef of string * ty list           (* named function used as a value *)
  | XCall of callee * targ list * conv list
  | XField of texpr * int * string       (* struct field *)
  | XTupleGet of texpr * int
  | XIndex of texpr * texpr
  | XSlice of texpr * texpr * texpr
  | XTuple of texpr list
  | XArray of texpr list
  | XStruct of string * ty list * texpr list
  | XVariant of string * ty list * int * texpr list
  | XIf of texpr * texpr * texpr
  | XBlock of tstmt list * texpr
  | XMatch of texpr * tarm list
  | XLambda of lambda
  | XBin of binop * texpr * texpr       (* on primitive types only *)
  | XNeg of texpr
  | XNot of texpr
  | XTry of texpr                        (* yields Result[T, E] *)
  | XConv of texpr                       (* numeric conversion to [ty] *)
  | XFail of texpr                       (* fail(e) *)
  | XComp of texpr * tcomp list          (* array comprehension *)
  | XNone
  | XPack of texpr                       (* a value of a type implementing the trait, boxed as [ty] = any Trait *)

and conv = { cfrom : ty; cfn : string; cto : ty }  (* From[cfrom] for cto, applied on propagation *)

and callee =
  | CFn of string * ty list              (* global function, type arguments *)
  | CBuiltin of string * ty list
  | CTrait of string * ty list * string * ty   (* trait, trait args, method, Self *)
  | CClosure of texpr

and targ = { amode : mode; a : texpr }

and tcomp = { cvar : tpat; csrc : titer; ccond : texpr option }

and titer = IRange of texpr * texpr | IArray of texpr * mode

and lambda = {
  lparams : var list;
  lbody : texpr;
  lcaps : var list;
  lfn : fnty;
  lname : string;                        (* unique name for generated code *)
}

and tarm = { pat : tpat; guard : texpr option; body : texpr }

and tpat =
  | TPWild
  | TPVar of var
  | TPLit of lit * ty
  | TPVariant of string * ty list * int * tpat list
  | TPStruct of string * ty list * tpat list
  | TPTuple of tpat list
  | TPErrType of ty * tpat               (* inside Err on a union: matches that member type *)

and tstmt = { st : ts; sl : loc }

and ts =
  | SLet of tpat * texpr
  | SVar of var * texpr
  | SAssign of place * texpr
  | SExpr of texpr
  | SReturn of texpr
  | SBreak
  | SContinue
  | SWhile of texpr * texpr
  | SFor of tpat * titer * texpr
  | SAssert of texpr * string
  | SAssertFails of ty * texpr
  | SCheck of texpr
  | SLocalFn of var * lambda
  | SLend of texpr                       (* lend [mut] place: the result of a lend function (4.6) *)

(* A place starts at a variable, or at the result of a lend mut call ([via]), whose
   root is then the variable that call lends from. *)
and place = { root : var; via : texpr option; path : proj list; pty : ty }

and proj = PField of int * string | PTupleIx of int | PIndex of texpr

(* ---------- declarations ---------- *)

type field_info = { fname_ : string; fty : ty }

type variant_info = { vname_ : string; vfields : field_info list; vnamed : bool; vindex : int }

type tdecl_body = DStruct of field_info list | DData of variant_info list | DAlias of ty

type tdecl = {
  dname : string;
  dparams : string list;
  mutable dbody : tdecl_body;
  dexport : bool;
  dopen : bool;
  dloc : loc;
  dmodule : string;
}

type fsig = {
  sname : string;              (* unique global name *)
  sdisplay : string;           (* name as written *)
  stparams : (string * (string * ty list) list) list;   (* name, bounds (trait, args) *)
  sparams : (mode * string * ty * expr option) list;
  sret : ty;
  mutable seff : eff;
  sdeclared : bool;            (* effects were written in the signature *)
  sexport : bool;
  slend : bool option;         (* Some false: -> lend T; Some true: -> lend mut T (4.6) *)
  sloc : loc;
  smodule : string;
}

type tfn = {
  fsig : fsig;
  fparams : var list;
  mutable fbody : texpr;
}

type trait_info = {
  trname_ : string;
  trparams : string list;
  trmethods_ : (string * fsig) list;    (* method sigs mention TParam "Self" *)
}

type impl_info = {
  itparams : (string * (string * ty list) list) list;
  itrait_ : string;
  itargs_ : ty list;
  ifor_ : ty;
  imethods_ : (string * string) list;   (* method name -> global fn name *)
  iloc_ : loc;
}

type tprog = {
  decls : (string, tdecl) Hashtbl.t;
  fns : (string, tfn) Hashtbl.t;
  fn_order : string list;
  traits : (string, trait_info) Hashtbl.t;
  impls : impl_info list;
  tests : (string * texpr * loc) list;
  main : string option;
  lambdas : lambda list;
}
