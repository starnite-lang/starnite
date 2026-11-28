(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Exhaustiveness and reachability of match arms: Maranget's usefulness algorithm (section 5.5). *)

open Types

(* KLen n is an array of exactly n elements. *)
type ctor = KVariant of int | KLit of string | KSingle | KErr of string | KLen of int

(* V ps is an array pattern that ends in `..`: the elements ps, and any number after them. *)
type cpat = W | C of ctor * cpat list | V of cpat list

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

let rec of_tpat = function
  | TPWild | TPVar _ -> W
  | TPLit (LBool b, _) -> C (KVariant (if b then 1 else 0), [])
  | TPLit (LUnit, _) -> C (KSingle, [])
  | TPLit (l, t) -> C (KLit (lit_key l t), [])
  | TPVariant (_, _, i, ps) -> C (KVariant i, List.map of_tpat ps)
  | TPStruct (_, _, ps) | TPTuple ps -> C (KSingle, List.map of_tpat ps)
  | TPErrType (t, p) -> C (KErr (show_ty t), [ of_tpat p ])
  | TPArray ([], true) -> W
  | TPArray (ps, false) -> C (KLen (List.length ps), List.map of_tpat ps)
  | TPArray (ps, true) -> V (List.map of_tpat ps)

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
  match (k, repr t) with
  | KLen n, TArray e -> List.init n (fun _ -> e)
  | _ ->
  match ctors decls t with
  | Some cs -> (match List.find_opt (fun (k', _, _) -> k' = k) cs with Some (_, ts, _) -> ts | None -> [])
  | None -> []

let specialize decls t k (rows : cpat list list) =
  let n = List.length (arity_of decls t k) in
  List.filter_map
    (fun row ->
      match row with
      | C (k', args) :: rest -> if k = k' then Some (args @ rest) else None
      | V ps :: rest -> (
          (* the elements it names, and whatever the rest of an array this long holds *)
          match k with
          | KLen _ when List.length ps <= n -> Some (ps @ List.init (n - List.length ps) (fun _ -> W) @ rest)
          | _ -> None)
      | W :: rest -> Some (List.init n (fun _ -> W) @ rest)
      | [] -> None)
    rows

let default_rows rows = List.filter_map (function W :: rest -> Some rest | _ -> None) rows

(* Arrays come in every length, but the patterns of a match tell only so many apart: with L the
   most elements any of them names, each length up to L is a case of its own, and all the longer
   ones are one case, since only a pattern that ends in `..` matches them and it looks at none of
   their elements past L. That case is stood for by the length L + 1. None when no row begins
   with an array pattern. *)
let longest rows =
  List.fold_left
    (fun acc row ->
      match row with
      | C (KLen n, _) :: _ -> Some (max n (Option.value acc ~default:0))
      | V ps :: _ -> Some (max (List.length ps) (Option.value acc ~default:0))
      | _ -> acc)
    None rows

let rec useful decls (rows : cpat list list) (v : cpat list) (tys : ty list) : bool =
  match (v, tys) with
  | [], _ -> rows = []
  | p :: vs, t :: ts -> (
      match p with
      | C (k, args) -> useful decls (specialize decls t k rows) (args @ vs) (arity_of decls t k @ ts)
      | V ps ->
          let k = List.length ps in
          let top = max k (match longest rows with Some l -> l + 1 | None -> 0) in
          List.exists
            (fun n ->
              let ats = arity_of decls t (KLen n) in
              useful decls (specialize decls t (KLen n) rows) (ps @ List.init (n - k) (fun _ -> W) @ vs) (ats @ ts))
            (List.init (top - k + 1) (fun i -> k + i))
      | W when longest rows <> None ->
          let top = Option.get (longest rows) + 1 in
          List.exists
            (fun n ->
              let ats = arity_of decls t (KLen n) in
              useful decls (specialize decls t (KLen n) rows) (List.map (fun _ -> W) ats @ vs) (ats @ ts))
            (List.init (top + 1) Fun.id)
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

(* A missing case, for the error message: one value for each column that no row matches, or None
   when the rows cover everything. *)
let rec missing decls (rows : cpat list list) (tys : ty list) : string list option =
  match tys with
  | [] -> if rows = [] then Some [] else None
  | t :: ts -> (
      let split n ws = (List.filteri (fun i _ -> i < n) ws, List.filteri (fun i _ -> i >= n) ws) in
      let present = List.filter_map (function C (k, _) :: _ -> Some k | _ -> None) rows in
      match (longest rows, ctors decls t) with
      | Some l, _ ->
          List.find_map
            (fun n ->
              let ats = arity_of decls t (KLen n) in
              match missing decls (specialize decls t (KLen n) rows) (ats @ ts) with
              | Some ws ->
                  let elems, rest = split n ws in
                  (* the longest length stands for every longer one too *)
                  Some (("[" ^ String.concat ", " (if n = l + 1 then elems @ [ ".." ] else elems) ^ "]") :: rest)
              | None -> None)
            (List.init (l + 2) Fun.id)
      | None, Some all when all <> [] && List.for_all (fun (k, _, _) -> List.mem k present) all ->
          List.find_map
            (fun (k, ats, name) ->
              match missing decls (specialize decls t k rows) (ats @ ts) with
              | Some ws ->
                  let args, rest = split (List.length ats) ws in
                  let shown =
                    if args = [] then name
                    else if name = "(...)" then "(" ^ String.concat ", " args ^ ")"
                    else name ^ "(" ^ String.concat ", " args ^ ")"
                  in
                  Some (shown :: rest)
              | None -> None)
            all
      | None, cs -> (
          match missing decls (default_rows rows) ts with
          | Some rest ->
              (* a constructor that no row names, where there is one to show *)
              let shown =
                match cs with
                | Some all when present <> [] -> (
                    match List.find_opt (fun (k, _, _) -> not (List.mem k present)) all with
                    | Some (_, [], name) -> name
                    | Some (_, ats, name) -> name ^ "(" ^ String.concat ", " (List.map (fun _ -> "_") ats) ^ ")"
                    | None -> "_")
                | _ -> "_"
              in
              Some (shown :: rest)
          | None -> None))

let witness decls rows t = match missing decls rows [ t ] with Some [ w ] -> Some w | Some _ -> Some "_" | None -> None

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
