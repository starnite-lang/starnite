(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* The reference interpreter (section 21.1): a direct implementation of section 4.
   Values are immutable trees, so every assignment and argument is a deep copy;
   nothing is shared, reused or freed. It defines what a program means. *)

open Types
open Values

type value =
  | VInt of int64
  | VFloat of float
  | VBool of bool
  | VChar of int
  | VUnit
  | VStr of string
  | VArr of value array          (* never mutated in place *)
  | VTuple of value array
  | VStruct of value array
  | VVariant of int * value array
  | VClosure of lambda * (int * value ref) list * (string * ty) list
  | VFn of string * ty list
  | VErr of ty * value           (* a member of an error union *)

exception Failed of ty * value
exception Partial of value list * exn
exception Assert_failed of string * Syntax.loc
exception Return of value
exception Break
exception Continue

type env = {
  prog : tprog;
  vars : (int, value ref) Hashtbl.t;
  sub : (string * ty) list;      (* type arguments of the current generic instance *)
}

let out = Buffer.create 65536

(* Shared cells currently lent out by a long access (section 13.3), by identity. Each
   statement restores the list when it ends, as the C backend clears busy flags when
   the statement's frame ends. *)
let busy : value ref list ref = ref []

let cell_busy_trap l what = trap "shared cell busy" l ("a shared cell was " ^ what ^ " while it was lent out")
let flush_out () = print_string (Buffer.contents out); Buffer.clear out; flush stdout

let tsub env t = subst env.sub t

let get_var env (v : var) =
  match Hashtbl.find_opt env.vars v.vid with
  | Some r -> r
  | None -> failwith ("interp: unbound " ^ v.vname)

let bind env (v : var) x = Hashtbl.replace env.vars v.vid (ref x)

let as_int = function VInt i -> i | VChar c -> Int64.of_int c | VBool b -> if b then 1L else 0L | _ -> failwith "int"
let as_float = function VFloat f -> f | _ -> failwith "float"
let as_bool = function VBool b -> b | _ -> failwith "bool"
let as_str = function VStr s -> s | _ -> failwith "str"
let as_arr = function VArr a -> a | _ -> failwith "array"

let rec values_equal a b =
  match (a, b) with
  | VFloat x, VFloat y -> x = y
  | VArr xs, VArr ys | VTuple xs, VTuple ys | VStruct xs, VStruct ys ->
      Array.length xs = Array.length ys && Array.for_all2 values_equal xs ys
  | VVariant (i, xs), VVariant (j, ys) -> i = j && Array.for_all2 values_equal xs ys
  | VErr (t, x), VErr (u, y) -> ty_equal t u && values_equal x y
  | _ -> a = b

let compare_values (t : ty) a b =
  match (repr t, a, b) with
  | TInt k, VInt x, VInt y -> compare_int k x y
  | (TFloat | TF32), VFloat x, VFloat y ->
      (* as the C backend: (x > y) - (x < y), so NaN compares equal to everything *)
      (if x > y then 1 else 0) - (if x < y then 1 else 0)
  | TStr, VStr x, VStr y -> compare x y
  | _, VChar x, VChar y -> compare x y
  | _, VBool x, VBool y -> compare x y
  | _, VInt x, VInt y -> Int64.compare x y
  | _ -> failwith "compare"

let utf8_chars s =
  let n = String.length s in
  let rec go i acc =
    if i >= n then List.rev acc
    else let c, len = Lexer.utf8_decode s i in go (i + len) (c :: acc)
  in
  go 0 []

let char_str c = let b = Buffer.create 4 in Lexer.utf8_encode b c; Buffer.contents b

(* the same limit as STN_MAX_ALLOC in the runtime *)
let max_alloc = Int64.shift_left 1L 40
let too_large loc = trap "allocation too large" loc "the requested size is too large"

(* The same rule as stn_str_from_bytes in the runtime: bytes that do not start a
   well-formed UTF-8 sequence become U+FFFD. *)
let sanitize_utf8 (s : string) : string =
  let n = String.length s in
  let b = Buffer.create n in
  let i = ref 0 in
  while !i < n do
    let c = Char.code s.[!i] in
    if c < 0x80 then (Buffer.add_char b s.[!i]; incr i)
    else begin
      let len, min, cp0 =
        if c >= 0xC2 && c <= 0xDF then (2, 0x80, c land 0x1F)
        else if c >= 0xE0 && c <= 0xEF then (3, 0x800, c land 0x0F)
        else if c >= 0xF0 && c <= 0xF4 then (4, 0x10000, c land 0x07)
        else (0, 0, 0)
      in
      let ok = ref (len > 0 && !i + len <= n) and cp = ref cp0 in
      for k = 1 to len - 1 do
        if !ok then begin
          let d = Char.code s.[!i + k] in
          if d land 0xC0 <> 0x80 then ok := false else cp := (!cp lsl 6) lor (d land 0x3F)
        end
      done;
      if !ok && (!cp < min || !cp > 0x10FFFF || (!cp >= 0xD800 && !cp <= 0xDFFF)) then ok := false;
      if !ok then (Buffer.add_string b (String.sub s !i len); i := !i + len)
      else (Buffer.add_string b "\xEF\xBF\xBD"; incr i)
    end
  done;
  Buffer.contents b

let is_boundary s i = i = String.length s || i = 0 || (Char.code s.[i] land 0xC0 <> 0x80)

(* ---------- traits ---------- *)

let resolve env trait targs meth self = Typecheck.impl_method_in env.prog.impls trait targs meth self

let rec show_value env (t : ty) (v : value) : string =
  let t = tsub env t in
  match (repr t, v) with
  | TInt k, VInt i -> int_to_string k i
  | TFloat, VFloat f -> float_to_string f
  | TF32, VFloat f -> f32_to_string f
  | TBool, VBool b -> if b then "true" else "false"
  | TChar, VChar c -> char_str c
  | TUnit, _ -> "()"
  | TStr, VStr s -> s
  | TDur, VInt n -> Int64.to_string n ^ "ns"
  | TBytes, VInt n -> Int64.to_string n ^ "b"
  | TTuple ts, VTuple vs -> "(" ^ String.concat ", " (List.mapi (fun i t -> show_value env t vs.(i)) ts) ^ ")"
  | TErr _, VErr (et, x) -> show_value env et x
  | _ -> (
      match resolve env "Show" [] "show" t with
      | Some (f, targs) -> as_str (call_fn env f targs [ v ] Syntax.noloc)
      | None -> "<" ^ show_ty t ^ ">")

(* ---------- calls ---------- *)

and call_fn env (name : string) (targs : ty list) (args : value list) loc : value =
  let tf = match Hashtbl.find_opt env.prog.fns name with Some f -> f | None -> failwith ("interp: no function " ^ name) in
  let sub = List.combine (List.map fst tf.fsig.stparams) targs in
  let env' = { env with vars = Hashtbl.create 16; sub } in
  List.iter2 (fun v a -> bind env' v a) tf.fparams args;
  try eval env' tf.fbody with Return v -> v

(* A call of a user function with mut parameters: run it, then read back the
   final values of the mut parameters. *)
and invoke env (tf : tfn) sub (vals : value list) : value * value list =
  let env' = { env with vars = Hashtbl.create 16; sub } in
  List.iter2 (fun v a -> bind env' v a) tf.fparams vals;
  let outs () = List.map (fun (v : var) -> !(get_var env' v)) tf.fparams in
  match eval env' tf.fbody with
  | r -> (r, outs ())
  | exception Return r -> (r, outs ())
  | exception (Failed _ as e) -> raise (Partial (outs (), e))

and invoke_closure env (lam : lambda) caps sub (vals : value list) : value * value list =
  let env' = { env with vars = Hashtbl.create 16; sub } in
  List.iter (fun (id, r) -> Hashtbl.replace env'.vars id r) caps;
  List.iter2 (fun v a -> bind env' v a) lam.lparams vals;
  let outs () = List.map (fun (v : var) -> !(get_var env' v)) lam.lparams in
  match eval env' lam.lbody with
  | r -> (r, outs ())
  | exception Return r -> (r, outs ())
  | exception (Failed _ as e) -> raise (Partial (outs (), e))

and apply_convs env (convs : conv list) f =
  try f ()
  with Failed (t, v) -> (
    match List.find_opt (fun cv -> ty_equal (tsub env cv.cfrom) t) convs with
    | Some cv ->
        let v' = call_fn env cv.cfn [] [ v ] Syntax.noloc in
        raise (Failed (tsub env cv.cto, v'))
    | None -> raise (Failed (t, v)))

and eval_call env (cl : callee) (targs : targ list) convs loc : value =
  apply_convs env convs (fun () ->
      let places = List.map (fun ta -> if ta.amode = MMut then (let p = place_of_expr env ta.a in hold_busy env ta.a; Some p) else None) targs in
      let vals =
        match cl with
        | CClosure _ -> []
        | _ -> List.map2 (fun ta p -> match p with Some (get, _) -> get () | None -> eval env ta.a) targs places
      in
      let fval = match cl with CClosure f -> Some (eval env f) | _ -> None in
      let vals = match cl with CClosure _ -> List.map2 (fun ta p -> match p with Some (get, _) -> get () | None -> eval env ta.a) targs places | _ -> vals in
      let write_back outs =
        let rec go ps os =
          match (ps, os) with
          | Some (_, set) :: ps, o :: os -> set o; go ps os
          | None :: ps, _ :: os -> go ps os
          | _ -> ()
        in
        go places outs
      in
      let run f = match f () with
        | (r, outs) -> write_back outs; r
        | exception Partial (outs, e) -> write_back outs; raise e
      in
      match cl with
      | CFn (name, tys) ->
          let tf = Hashtbl.find env.prog.fns name in
          let sub = List.combine (List.map fst tf.fsig.stparams) (List.map (tsub env) tys) in
          run (fun () -> invoke env tf sub vals)
      | CBuiltin (name, tys) -> run (fun () -> builtin env name (List.map (tsub env) tys) vals loc)
      | CTrait (tr, ta, m, self) ->
          let self = tsub env self in
          let ta = List.map (tsub env) ta in
          (match resolve env tr ta m self with
           | Some (f, ftys) ->
               let tf = Hashtbl.find env.prog.fns f in
               let sub = List.combine (List.map fst tf.fsig.stparams) ftys in
               run (fun () -> invoke env tf sub vals)
           | None -> run (fun () -> (prim_trait env tr m self vals loc, vals)))
      | CClosure _ -> (
          match fval with
          | Some (VClosure (lam, caps, sub)) -> run (fun () -> invoke_closure env lam caps sub vals)
          | Some (VFn (name, tys)) ->
              let tf = Hashtbl.find env.prog.fns name in
              let sub = List.combine (List.map fst tf.fsig.stparams) tys in
              run (fun () -> invoke env tf sub vals)
          | _ -> failwith "interp: call of a non-function"))

(* Built-in trait methods on primitive, tuple and derived types. *)
and prim_trait env tr m self vals loc : value =
  match (tr, vals) with
  | "Show", [ v ] -> VStr (show_value env self v)
  | "Eq", [ a; b ] -> VBool (values_equal a b)
  | "Ord", [ a; b ] -> VInt (Int64.of_int (compare_values self a b))
  | "Hash", [ v ] -> VInt (Int64.of_int (Hashtbl.hash v))
  | "Default", [] -> (
      match repr self with
      | TInt _ -> VInt 0L | TFloat | TF32 -> VFloat 0.0 | TStr -> VStr "" | TBool -> VBool false | TChar -> VChar 0
      | _ -> VUnit)
  | ("Add" | "Sub" | "Mul" | "Div"), [ a; b ] ->
      let op = match tr with "Add" -> Add | "Sub" -> Sub | "Mul" -> Mul | _ -> Div in
      binop env op self a b loc
  | _ -> failwith ("interp: no implementation of " ^ tr ^ "." ^ m ^ " for " ^ show_ty self)

and binop env op (t : ty) a b loc : value =
  match (repr t, a, b) with
  | (TInt k), VInt x, VInt y -> (
      match op with
      | Add -> VInt (add k loc x y) | Sub -> VInt (sub k loc x y) | Mul -> VInt (mul k loc x y)
      | Div -> VInt (div k loc x y) | Mod -> VInt (rem k loc x y)
      | AddW -> VInt (wrap k (Int64.add x y)) | SubW -> VInt (wrap k (Int64.sub x y)) | MulW -> VInt (wrap k (Int64.mul x y))
      | _ -> failwith "binop")
  | (TDur | TBytes), VInt x, VInt y -> (
      match op with
      | Add -> VInt (add IInt loc x y) | Sub -> VInt (sub IInt loc x y)
      | _ -> failwith "binop dur")
  | TFloat, VFloat x, VFloat y -> (
      match op with
      | Add -> VFloat (x +. y) | Sub -> VFloat (x -. y) | Mul -> VFloat (x *. y) | Div -> VFloat (x /. y)
      | Mod -> VFloat (Float.rem x y)
      | _ -> failwith "binop")
  | TF32, VFloat x, VFloat y -> (
      let r = match op with
        | Add -> x +. y | Sub -> x -. y | Mul -> x *. y | Div -> x /. y | Mod -> Float.rem x y
        | _ -> failwith "binop" in
      VFloat (f32_round r))
  | TStr, VStr x, VStr y when op = Add -> VStr (x ^ y)
  | _ -> failwith ("interp: binop on " ^ show_ty t)

(* ---------- places ---------- *)

(* get and set functions for a place expression *)
and cell_root env (e : texpr) : (value ref * Syntax.loc) option =
  match e.e with
  | XVar v when v.vcell -> Some (get_var env v, e.l)
  | XField (b, _, _) | XTupleGet (b, _) | XIndex (b, _) -> cell_root env b
  | _ -> None

and hold_busy env (e : texpr) =
  match cell_root env e with Some (r, _) -> busy := r :: !busy | None -> ()

and place_of_expr env (e : texpr) : (unit -> value) * (value -> unit) =
  (match cell_root env e with
   | Some (r, l) when List.memq r !busy -> cell_busy_trap l "accessed"
   | _ -> ());
  match e.e with
  | XVar v ->
      let r = get_var env v in
      ((fun () -> !r), fun x -> r := x)
  | XField (b, i, _) ->
      let get, set = place_of_expr env b in
      ( (fun () -> match get () with VStruct fs -> fs.(i) | _ -> failwith "field"),
        fun x -> match get () with VStruct fs -> let fs = Array.copy fs in fs.(i) <- x; set (VStruct fs) | _ -> failwith "field" )
  | XTupleGet (b, i) ->
      let get, set = place_of_expr env b in
      ( (fun () -> match get () with VTuple fs -> fs.(i) | _ -> failwith "tuple"),
        fun x -> match get () with VTuple fs -> let fs = Array.copy fs in fs.(i) <- x; set (VTuple fs) | _ -> failwith "tuple" )
  | XIndex (b, ix) ->
      let get, set = place_of_expr env b in
      let i = as_int (eval env ix) in
      let check a = if Int64.compare i 0L < 0 || Int64.compare i (Int64.of_int (Array.length a)) >= 0 then
          trap "index out of range" e.l (Printf.sprintf "index %Ld, length %d" i (Array.length a)) in
      ( (fun () -> let a = as_arr (get ()) in check a; a.(Int64.to_int i)),
        fun x -> let a = Array.copy (as_arr (get ())) in check a; a.(Int64.to_int i) <- x; set (VArr a) )
  | _ ->
      let v = eval env e in
      ((fun () -> v), fun _ -> ())

and assign env (p : place) (x : value) =
  let r = get_var env p.root in
  let rec upd (cur : value) path =
    match path with
    | [] -> x
    | PField (i, _) :: rest -> (
        match cur with VStruct fs -> let fs = Array.copy fs in fs.(i) <- upd fs.(i) rest; VStruct fs | _ -> failwith "assign field")
    | PTupleIx i :: rest -> (
        match cur with VTuple fs -> let fs = Array.copy fs in fs.(i) <- upd fs.(i) rest; VTuple fs | _ -> failwith "assign tuple")
    | PIndex ix :: rest ->
        let a = Array.copy (as_arr cur) in
        let i = as_int (eval env ix) in
        if Int64.compare i 0L < 0 || Int64.compare i (Int64.of_int (Array.length a)) >= 0 then
          trap "index out of range" ix.l (Printf.sprintf "index %Ld, length %d" i (Array.length a));
        a.(Int64.to_int i) <- upd a.(Int64.to_int i) rest;
        VArr a
  in
  (* indices are evaluated before the old value is read *)
  r := upd !r p.path

(* ---------- expressions ---------- *)

and eval env (te : texpr) : value =
  match te.e with
  | XLit l -> (
      match l with
      | LInt s -> (
          match repr (tsub env te.ty) with
          | TFloat | TF32 -> VFloat (float_of_string s)
          | _ -> VInt (parse_int_lit s))
      | LFloat f -> VFloat (if repr te.ty = TF32 then f32_round f else f)
      | LStr s -> VStr s
      | LChar c -> VChar c
      | LBool b -> VBool b
      | LUnit -> VUnit
      | LDur (n, u) -> VInt (dur_value n u))
  | XFStr ps -> VStr (String.concat "" (List.map (fun p -> as_str (eval env p)) ps))
  | XVar v ->
      let r = get_var env v in
      if v.vcell && List.memq r !busy then cell_busy_trap te.l "accessed";
      !r
  | XFnRef (n, ts) -> VFn (n, List.map (tsub env) ts)
  | XCall (cl, args, convs) -> eval_call env cl args convs te.l
  | XField (b, i, _) -> (match eval env b with VStruct fs -> fs.(i) | _ -> failwith "field")
  | XTupleGet (b, i) -> (match eval env b with VTuple fs -> fs.(i) | _ -> failwith "tuple")
  | XIndex (b, ix) ->
      let a = as_arr (eval env b) in
      let i = as_int (eval env ix) in
      if Int64.compare i 0L < 0 || Int64.compare i (Int64.of_int (Array.length a)) >= 0 then
        trap "index out of range" te.l (Printf.sprintf "index %Ld, length %d" i (Array.length a));
      a.(Int64.to_int i)
  | XSlice (b, lo, hi) -> (
      let v = eval env b in
      let lo = as_int (eval env lo) and hi = as_int (eval env hi) in
      match v with
      | VArr a ->
          let n = Int64.of_int (Array.length a) in
          if Int64.compare lo 0L < 0 || Int64.compare hi n > 0 || Int64.compare lo hi > 0 then
            trap "index out of range" te.l (Printf.sprintf "slice %Ld..%Ld, length %Ld" lo hi n);
          VArr (Array.sub a (Int64.to_int lo) (Int64.to_int (Int64.sub hi lo)))
      | VStr s ->
          let n = Int64.of_int (String.length s) in
          if Int64.compare lo 0L < 0 || Int64.compare hi n > 0 || Int64.compare lo hi > 0 then
            trap "index out of range" te.l (Printf.sprintf "slice %Ld..%Ld, length %Ld" lo hi n);
          let lo = Int64.to_int lo and hi = Int64.to_int hi in
          if not (is_boundary s lo && is_boundary s hi) then trap "index out of range" te.l "slice does not fall on character boundaries";
          VStr (String.sub s lo (hi - lo))
      | _ -> failwith "slice")
  | XTuple es -> VTuple (Array.of_list (List.map (eval env) es))
  | XArray es -> VArr (Array.of_list (List.map (eval env) es))
  | XStruct (_, _, es) -> VStruct (Array.of_list (List.map (eval env) es))
  | XVariant (_, _, i, es) -> VVariant (i, Array.of_list (List.map (eval env) es))
  | XIf (c, a, b) -> if as_bool (eval env c) then eval env a else eval env b
  | XBlock (ss, v) -> List.iter (exec env) ss; eval env v
  | XMatch (s, arms) ->
      let v = eval env s in
      let rec go = function
        | [] -> failwith "interp: no arm matched"
        | a :: rest ->
            if match_pat env a.pat v && (match a.guard with Some g -> as_bool (eval env g) | None -> true) then eval env a.body
            else go rest
      in
      go arms
  | XLambda lam ->
      let caps = List.map (fun (v : var) -> (v.vid, get_var env v)) lam.lcaps in
      VClosure (lam, caps, env.sub)
  | XBin (And, a, b) -> VBool (as_bool (eval env a) && as_bool (eval env b))
  | XBin (Or, a, b) -> VBool (as_bool (eval env a) || as_bool (eval env b))
  | XBin (((Eq | Ne | Lt | Le | Gt | Ge) as op), a, b) ->
      let x = eval env a and y = eval env b in
      let t = tsub env a.ty in
      let r =
        match op with
        | Eq -> values_equal x y
        | Ne -> not (values_equal x y)
        | _ -> (
            (* NaN compares false *)
            match (x, y) with
            | VFloat fx, VFloat fy -> (match op with Lt -> fx < fy | Le -> fx <= fy | Gt -> fx > fy | _ -> fx >= fy)
            | _ ->
                let c = compare_values t x y in
                match op with Lt -> c < 0 | Le -> c <= 0 | Gt -> c > 0 | _ -> c >= 0)
      in
      VBool r
  | XBin (op, a, b) ->
      let x = eval env a in
      let y = eval env b in
      binop env op (tsub env te.ty) x y te.l
  | XNeg a -> (
      match (repr (tsub env te.ty), eval env a) with
      | TInt k, VInt x -> VInt (sub k te.l 0L x)
      | _, VFloat f -> VFloat (-.f)
      | _ -> failwith "neg")
  | XNot a -> VBool (not (as_bool (eval env a)))
  | XTry a -> (
      match eval env a with
      | v -> VVariant (0, [| v |])
      | exception Failed (t, v) ->
          let ety = match repr (tsub env te.ty) with TNamed ("Result", [ _; e ]) -> e | _ -> t in
          let v = match repr ety with TErr _ -> VErr (t, v) | _ -> v in
          VVariant (1, [| v |]))
  | XConv a -> convert env (tsub env a.ty) (tsub env te.ty) (eval env a) te.l
  | XFail a -> (
      let v = eval env a in
      match v with
      | VErr (t, x) -> raise (Failed (t, x))
      | _ -> raise (Failed (tsub env a.ty, v)))
  | XComp (body, comps) ->
      let acc = ref [] in
      let rec go = function
        | [] -> acc := eval env body :: !acc
        | cp :: rest ->
            iterate env cp.csrc (fun x ->
                if match_pat env cp.cvar x then
                  match cp.ccond with Some c when not (as_bool (eval env c)) -> () | _ -> go rest)
      in
      go comps;
      VArr (Array.of_list (List.rev !acc))
  | XNone -> VUnit

and iterate env (src : titer) (f : value -> unit) =
  match src with
  | IRange (a, b) ->
      let lo = as_int (eval env a) and hi = as_int (eval env b) in
      let k = match repr (tsub env a.ty) with TInt k -> k | _ -> IInt in
      let i = ref lo in
      while compare_int k !i hi < 0 do
        f (VInt !i);
        i := Int64.add !i 1L
      done
  | IArray (a, _) ->
      let arr = as_arr (eval env a) in
      Array.iter f arr

and convert env (from : ty) (target : ty) (v : value) loc : value =
  let range_trap () = trap "integer overflow" loc (Printf.sprintf "the value does not fit in %s" (show_ty target)) in
  match (repr from, repr target, v) with
  | TInt fk, TInt tk, VInt x ->
      (* compare as mathematical integers *)
      let neg = ikind_signed fk && Int64.compare x 0L < 0 in
      let big_unsigned = fk = U64 && Int64.compare x 0L < 0 in
      (match tk with
       | U64 -> if neg then range_trap ()
       | IInt | I64 -> if big_unsigned then range_trap ()
       | _ -> if big_unsigned || not (fits tk x) then range_trap ());
      VInt x
  | (TBool | TChar), TInt tk, _ ->
      let x = as_int v in
      if not (fits tk x) then range_trap ();
      VInt x
  | TInt fk, (TFloat | TF32), VInt x ->
      let f = if fk = U64 && Int64.compare x 0L < 0 then Int64.to_float (Int64.shift_right_logical x 1) *. 2.0 +. Int64.to_float (Int64.logand x 1L) else Int64.to_float x in
      VFloat (if repr target = TF32 then f32_round f else f)
  | (TFloat | TF32), TInt tk, VFloat f ->
      if Float.is_nan f then range_trap ();
      let t = Float.trunc f in
      let lo = Int64.to_float (min_of tk) in
      let hi = if tk = U64 then 18446744073709551616.0 else Int64.to_float (max_of tk) +. 1.0 in
      if t < lo || t >= hi then range_trap ();
      if tk = U64 && t >= 9223372036854775808.0 then VInt (Int64.add (Int64.of_float (t -. 9223372036854775808.0)) Int64.min_int)
      else VInt (Int64.of_float t)
  | (TFloat | TF32), TFloat, VFloat f -> VFloat f
  | (TFloat | TF32), TF32, VFloat f -> VFloat (f32_round f)
  | TBool, (TFloat | TF32), VBool b -> VFloat (if b then 1.0 else 0.0)
  | TChar, (TFloat | TF32), VChar c -> VFloat (float_of_int c)
  | TInt _, TChar, VInt x ->
      if Int64.compare x 0L < 0 || Int64.compare x 0x10FFFFL > 0 || (Int64.compare x 0xD800L >= 0 && Int64.compare x 0xDFFFL <= 0) then
        trap "invalid character" loc (Printf.sprintf "%Ld is not a Unicode scalar value" x);
      VChar (Int64.to_int x)
  | (TDur | TBytes), TInt _, VInt x -> VInt x
  | TInt _, (TDur | TBytes), VInt x -> VInt x
  | _ -> failwith ("convert " ^ show_ty from ^ " to " ^ show_ty target)

(* ---------- patterns ---------- *)

and match_pat env (p : tpat) (v : value) : bool =
  match (p, v) with
  | TPWild, _ -> true
  | TPVar var, _ -> bind env var v; true
  | TPLit (l, t), _ -> values_equal (eval env { e = XLit l; ty = t; l = Syntax.noloc }) v
  | TPVariant (_, _, i, ps), VVariant (j, vs) -> i = j && List.for_all2 (fun p v -> match_pat env p v) ps (Array.to_list vs)
  | TPVariant (_, _, i, ps), _ -> false
  | TPStruct (_, _, ps), VStruct vs | TPTuple ps, VTuple vs -> List.for_all2 (fun p v -> match_pat env p v) ps (Array.to_list vs)
  | TPTuple [], VUnit -> true
  | TPErrType (t, p), VErr (t', x) -> ty_equal (tsub env t) t' && match_pat env p x
  | TPErrType (_, p), _ -> match_pat env p v
  | _ -> false

(* ---------- statements ---------- *)

and exec env (s : tstmt) : unit =
  let saved = !busy in
  Fun.protect ~finally:(fun () -> busy := saved) (fun () -> exec_ env s)

and exec_ env (s : tstmt) : unit =
  match s.st with
  | SLet (p, e) ->
      let v = eval env e in
      if not (match_pat env p v) then trap "pattern mismatch" s.sl "the value does not match the let pattern"
  | SVar (v, e) -> bind env v (eval env e)
  | SAssign (p, e) ->
      let x = eval env e in
      if p.root.vcell && List.memq (get_var env p.root) !busy then cell_busy_trap s.sl "assigned";
      assign env p x
  | SExpr e -> ignore (eval env e)
  | SReturn e -> raise (Return (eval env e))
  | SBreak -> raise Break
  | SContinue -> raise Continue
  | SWhile (c, body) -> (
      try
        while as_bool (eval env c) do
          try ignore (eval env body) with Continue -> ()
        done
      with Break -> ())
  | SFor (p, src, body) -> (
      try
        match (src, p) with
        | IArray (arr, MMut), TPVar var ->
            (* for x in mut xs: each element is a mutable place *)
            let get, set = place_of_expr env arr in
            hold_busy env arr;
            let n = Array.length (as_arr (get ())) in
            for i = 0 to n - 1 do
              let a = as_arr (get ()) in
              if i < Array.length a then begin
                bind env var a.(i);
                (try ignore (eval env body) with Continue -> ());
                let a = Array.copy (as_arr (get ())) in
                if i < Array.length a then (a.(i) <- !(get_var env var); set (VArr a))
              end
            done
        | _ ->
            iterate env src (fun x ->
                ignore (match_pat env p x);
                try ignore (eval env body) with Continue -> ())
      with Break -> ())
  | SAssert (e, _) ->
      if not (as_bool (eval env e)) then raise (Assert_failed (describe_assert env e, s.sl))
  | SAssertFails (t, e) -> (
      match eval env e with
      | _ -> raise (Assert_failed ("expected a failure with " ^ show_ty t ^ ", but the expression succeeded", s.sl))
      | exception Failed (t', _) when ty_equal (tsub env t) t' -> ()
      | exception Failed (t', v) ->
          raise (Assert_failed (Printf.sprintf "expected a failure with %s, got %s: %s" (show_ty t) (show_ty t') (show_value env t' v), s.sl)))
  | SCheck e -> if not (as_bool (eval env e)) then trap "check failed" s.sl "the checked condition is false"
  | SLocalFn (v, lam) ->
      let caps = List.map (fun (cv : var) -> (cv.vid, get_var env cv)) lam.lcaps in
      bind env v (VClosure (lam, caps, env.sub))

(* When assert e fails, show the value of each side of a comparison (section 20.2). *)
and describe_assert env (e : texpr) : string =
  match e.e with
  | XBin ((Eq | Ne | Lt | Le | Gt | Ge), a, b) ->
      Printf.sprintf "assertion failed: left = %s, right = %s" (show_value env a.ty (eval env a)) (show_value env b.ty (eval env b))
  | XNot { e = XCall (CTrait ("Eq", _, _, t), [ a; b ], _); _ } | XCall (CTrait ("Eq", _, _, t), [ a; b ], _) ->
      Printf.sprintf "assertion failed: left = %s, right = %s" (show_value env t (eval env a.a)) (show_value env t (eval env b.a))
  | _ -> "assertion failed"

(* ---------- built-in functions ---------- *)

and builtin env name (tys : ty list) (vals : value list) loc : value * value list =
  let pure v = (v, vals) in
  match (name, vals) with
  | "print@Str", [ VStr s ] -> Buffer.add_string out s; Buffer.add_char out '\n';
      if Buffer.length out > 60000 then flush_out ();
      pure VUnit
  | "read_line@", [] -> (
      flush_out ();
      match In_channel.input_line stdin with
      | Some l -> pure (VVariant (1, [| VStr (sanitize_utf8 l) |]))
      | None -> pure (VVariant (0, [||])))
  | "clock_ns@", [] -> pure (VInt (Int64.of_float (Unix.gettimeofday () *. 1e9)))
  | "len@Array", [ VArr a ] -> pure (VInt (Int64.of_int (Array.length a)))
  | "push@Array", [ VArr a; x ] -> (VUnit, [ VArr (Array.append a [| x |]); x ])
  | "pop@Array", [ VArr a ] ->
      let n = Array.length a in
      if n = 0 then (VVariant (0, [||]), vals) else (VVariant (1, [| a.(n - 1) |]), [ VArr (Array.sub a 0 (n - 1)) ])
  | "insert@Array", [ VArr a; VInt i; x ] ->
      let n = Array.length a in
      if Int64.compare i 0L < 0 || Int64.compare i (Int64.of_int n) > 0 then trap "index out of range" loc (Printf.sprintf "index %Ld, length %d" i n);
      let i = Int64.to_int i in
      (VUnit, [ VArr (Array.concat [ Array.sub a 0 i; [| x |]; Array.sub a i (n - i) ]); VInt (Int64.of_int i); x ])
  | "remove@Array", [ VArr a; VInt i ] ->
      let n = Array.length a in
      if Int64.compare i 0L < 0 || Int64.compare i (Int64.of_int n) >= 0 then trap "index out of range" loc (Printf.sprintf "index %Ld, length %d" i n);
      let i = Int64.to_int i in
      (a.(i), [ VArr (Array.append (Array.sub a 0 i) (Array.sub a (i + 1) (n - i - 1))); VInt (Int64.of_int i) ])
  | "clear@Array", [ VArr _ ] -> (VUnit, [ VArr [||] ])
  | "extend@Array", [ VArr a; VArr b ] -> (VUnit, [ VArr (Array.append a b); VArr b ])
  | "filled@Int", [ VInt n; x ] ->
      if Int64.compare n 0L < 0 then trap "index out of range" loc "negative length";
      if Int64.compare n max_alloc > 0 then too_large loc;
      pure (VArr (Array.make (Int64.to_int n) x))
  | "copy@T", [ x ] -> pure x
  | "unreachable@Str", [ VStr m ] -> trap "unreachable" loc m
  | "len@Str", [ VStr s ] -> pure (VInt (Int64.of_int (String.length s)))
  | "chars@Str", [ VStr s ] -> pure (VArr (Array.of_list (List.map (fun c -> VChar c) (utf8_chars s))))
  | "split@Str", [ VStr s; VStr sep ] ->
      if sep = "" then trap "invalid argument" loc "split with an empty separator";
      let parts = ref [] and st = ref 0 and i = ref 0 in
      let n = String.length s and m = String.length sep in
      while !i <= n - m do
        if String.sub s !i m = sep then (parts := String.sub s !st (!i - !st) :: !parts; i := !i + m; st := !i)
        else incr i
      done;
      parts := String.sub s !st (n - !st) :: !parts;
      pure (VArr (Array.of_list (List.rev_map (fun p -> VStr p) !parts)))
  | "join@Array", [ VArr xs; VStr sep ] -> pure (VStr (String.concat sep (List.map as_str (Array.to_list xs))))
  | "trim@Str", [ VStr s ] -> pure (VStr (String.trim s))
  | "contains@Str", [ VStr s; VStr sub ] ->
      let n = String.length s and m = String.length sub in
      let rec go i = i <= n - m && (String.sub s i m = sub || go (i + 1)) in
      pure (VBool (go 0))
  | "starts_with@Str", [ VStr s; VStr p ] -> pure (VBool (String.starts_with ~prefix:p s))
  | "ends_with@Str", [ VStr s; VStr p ] -> pure (VBool (String.ends_with ~suffix:p s))
  | "repeat@Str", [ VStr s; VInt n ] ->
      if Int64.compare n 0L < 0 then trap "invalid argument" loc "negative repeat count";
      if n > 0L && Int64.compare (Int64.of_int (String.length s)) (Int64.div max_alloc n) > 0 then too_large loc;
      let b = Buffer.create (String.length s * Int64.to_int n) in
      for _ = 1 to Int64.to_int n do Buffer.add_string b s done;
      pure (VStr (Buffer.contents b))
  | "parse_int@Str", [ VStr s ] -> (
      match (try Values.parse_int_text s with Exit -> raise (Failed (TNamed ("ParseError", []), VVariant (1, [| VStr s |])))) with
      | Some v -> pure (VInt v)
      | None -> raise (Failed (TNamed ("ParseError", []), VVariant (0, [| VStr s |]))))
  | "parse_float@Str", [ VStr s ] -> (
      let ok = s <> "" && String.for_all (fun ch -> (ch >= '0' && ch <= '9') || ch = '.' || ch = '-' || ch = '+' || ch = 'e' || ch = 'E') s in
      match (if ok then float_of_string_opt s else None) with
      | Some f -> pure (VFloat f)
      | None -> raise (Failed (TNamed ("ParseError", []), VVariant (0, [| VStr s |]))))
  | "sqrt@Float", [ VFloat x ] -> pure (VFloat (Float.sqrt x))
  | "sin@Float", [ VFloat x ] -> pure (VFloat (Float.sin x))
  | "cos@Float", [ VFloat x ] -> pure (VFloat (Float.cos x))
  | "tan@Float", [ VFloat x ] -> pure (VFloat (Float.tan x))
  | "exp@Float", [ VFloat x ] -> pure (VFloat (Float.exp x))
  | "log@Float", [ VFloat x ] -> pure (VFloat (Float.log x))
  | "pow@Float", [ VFloat x; VFloat y ] -> pure (VFloat (Float.pow x y))
  | "floor@Float", [ VFloat x ] -> pure (VFloat (Float.floor x))
  | "ceil@Float", [ VFloat x ] -> pure (VFloat (Float.ceil x))
  | "abs@Float", [ VFloat x ] -> pure (VFloat (Float.abs x))
  | "abs@Int", [ VInt x ] -> if x = Int64.min_int then overflow loc; pure (VInt (Int64.abs x))
  | _ -> failwith ("interp: built-in " ^ name ^ " is not implemented")
