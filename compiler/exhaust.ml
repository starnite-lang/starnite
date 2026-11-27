(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Exhaustiveness and reachability of match arms: Maranget's usefulness algorithm (section 5.5). *)

open Types

type ctor = KVariant of int | KLit of string | KSingle | KErr of string

type cpat = W | C of ctor * cpat list

(* One key per value, so that 1 and 0x1, or two F32 literals that round alike, or 0.0
   and -0.0, are the same constructor. *)
let lit_key (l : Syntax.lit) (t : ty) =
  let float_key f =
    let f = match repr t with TF32 -> Values.f32_round f | _ -> f in
    if f = 0.0 then "f0" else Printf.sprintf "f%h" f
  in
  match (l, repr t) with
  | LInt s, (TFloat | TF32) -> float_key (float_of_string s)
  | LInt s, _ -> "i" ^ Int64.to_string (Values.parse_int_lit s)
  | LFloat f, _ -> float_key f
  | LStr s, _ -> "s" ^ s
  | LChar c, _ -> "c" ^ string_of_int c
  | _ -> "?"

let array_case = ref 0

let rec of_tpat = function
  | TPWild | TPVar _ -> W
  | TPLit (LBool b, _) -> C (KVariant (if b then 1 else 0), [])
  | TPLit (LUnit, _) -> C (KSingle, [])
  | TPLit (l, t) -> C (KLit (lit_key l t), [])
  | TPVariant (_, _, i, ps) -> C (KVariant i, List.map of_tpat ps)
  | TPStruct (_, _, ps) | TPTuple ps -> C (KSingle, List.map of_tpat ps)
  | TPErrType (t, p) -> C (KErr (show_ty t), [ of_tpat p ])
  (* An array has no end of lengths, so its patterns are like literals: only [..] covers every
     array. Two patterns of one length are the same case only when neither tests its elements. *)
  | TPArray ([], true) -> W
  | TPArray (ps, rest) ->
      let open_ = List.for_all (fun p -> of_tpat p = W) ps in
      if open_ then C (KLit (Printf.sprintf "a%d%s" (List.length ps) (if rest then "+" else "")), [])
      else (incr array_case; C (KLit (Printf.sprintf "a#%d" !array_case), []))

(* All constructors of a type with their argument types; None when there are infinitely many. *)
let ctors decls t : (ctor * ty list * string) list option =
  match repr t with
  | TBool -> Some [ (KVariant 0, [], "false"); (KVariant 1, [], "true") ]
  | TUnit -> Some [ (KSingle, [], "()") ]
  | TTuple ts -> Some [ (KSingle, ts, "(...)") ]
  | TNamed (n, args) -> (
      match Hashtbl.find_opt decls n with
      | Some d -> (
          let s = List.combine d.dparams args in
          match d.dbody with
          | DStruct fs -> Some [ (KSingle, List.map (fun f -> subst s f.fty) fs, n) ]
          | DData vs -> Some (List.map (fun v -> (KVariant v.vindex, List.map (fun f -> subst s f.fty) v.vfields, v.vname_)) vs)
          | DAlias _ | DBuiltin -> None)
      | None -> None)
  | TErr ms -> Some (List.map (fun m -> (KErr (show_ty m), [ m ], show_ty m)) ms)
  | _ -> None

let arity_of decls t k =
  match ctors decls t with
  | Some cs -> (match List.find_opt (fun (k', _, _) -> k' = k) cs with Some (_, ts, _) -> ts | None -> [])
  | None -> []

let specialize decls t k (rows : cpat list list) =
  let n = List.length (arity_of decls t k) in
  List.filter_map
    (fun row ->
      match row with
      | C (k', args) :: rest -> if k = k' then Some (args @ rest) else None
      | W :: rest -> Some (List.init n (fun _ -> W) @ rest)
      | [] -> None)
    rows

let default_rows rows = List.filter_map (function W :: rest -> Some rest | _ -> None) rows

let rec useful decls (rows : cpat list list) (v : cpat list) (tys : ty list) : bool =
  match (v, tys) with
  | [], _ -> rows = []
  | p :: vs, t :: ts -> (
      match p with
      | C (k, args) -> useful decls (specialize decls t k rows) (args @ vs) (arity_of decls t k @ ts)
      | W -> (
          let present = List.filter_map (function C (k, _) :: _ -> Some k | _ -> None) rows in
          match ctors decls t with
          | Some all when all <> [] && List.for_all (fun (k, _, _) -> List.mem k present) all ->
              List.exists
                (fun (k, ats, _) ->
                  useful decls (specialize decls t k rows) (List.map (fun _ -> W) ats @ vs) (ats @ ts))
                all
          | _ -> useful decls (default_rows rows) vs ts))
  | _ -> false

(* A missing case, for the error message. *)
let rec witness decls (rows : cpat list list) (t : ty) : string option =
  if not (useful decls rows [ W ] [ t ]) then None
  else
    match ctors decls t with
    | Some all ->
        let found =
          List.find_map
            (fun (k, ats, name) ->
              let sub = specialize decls t k rows in
              if useful decls sub (List.map (fun _ -> W) ats) ats then
                let args =
                  match ats with
                  | [] -> ""
                  (* nothing matches this constructor at all: any arguments will do,
                     and recursing into a recursive type would not terminate *)
                  | _ when sub = [] -> "(" ^ String.concat ", " (List.map (fun _ -> "_") ats) ^ ")"
                  | [ at ] -> (match witness decls (List.map (function [ p ] -> [ p ] | p :: _ -> [ p ] | [] -> [ W ]) sub) at with Some w -> "(" ^ w ^ ")" | None -> "(_)")
                  | _ -> "(" ^ String.concat ", " (List.map (fun _ -> "_") ats) ^ ")"
                in
                Some (name ^ args)
              else None)
            all
        in
        (match found with Some f -> Some f | None -> Some "_")
    | None -> Some "_"

let check decls (t : ty) (arms : (tpat * bool) list) loc (arm_locs : Syntax.loc list) =
  let rows = ref [] in
  List.iteri
    (fun i (p, guarded) ->
      let cp = of_tpat p in
      if not (useful decls !rows [ cp ] [ t ]) then
        Syntax.error "E0206" (List.nth arm_locs i) "this arm is unreachable: earlier arms cover every value it matches";
      if not guarded then rows := !rows @ [ [ cp ] ])
    arms;
  match witness decls !rows t with
  | None -> ()
  | Some w -> Syntax.error "E0202" loc "match does not cover every case; %s is not matched" w
