(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* A model of counting, reuse and destination passing (sections 9 and 21.4), with properties P1
   and P2 tested on random programs.

   The spec asks for the model in a proof assistant, and for each property to be tested by random
   generation inside the model before any proof is tried. This is that second step on its own: an
   executable model, written in OCaml because no proof assistant is part of the build. Nothing
   here is proved.

   The calculus is first-order: integers, two data types (a list and a tree), `let`, `match`,
   calls, and parameters that are read-only or `take`. `mut` is left out. A program has two
   meanings:

   - the reference semantics, which builds values as trees and knows nothing of memory;
   - the counted semantics: the program is put in a normal form, count updates are inserted
     (section 9.2), cells taken apart are offered to constructors (9.3), and functions that return
     a constructor holding a call of themselves become loops over a destination (9.5). It then
     runs on a machine with a heap of counted cells, in which using a released cell, releasing
     one twice and lowering a count below zero are errors.

   P1: the counted program never touches a released cell, and when its result has been released
       the heap is empty.
   P2: the counted program, with reuse and destination passing, gives the value the reference
       semantics gives.

   The passes here are written from the spec, not taken from the compiler: the model tests the
   design, and the fuzzer (section 21.2) tests the compiler against the reference interpreter. *)

(* ---------- the calculus ---------- *)

type ty = TInt | TData of int

(* data types: constructors with the types of their fields *)
let decls : (string * (string * ty list) array) array =
  [| ("List", [| ("Nil", []); ("Cons", [ TInt; TData 0 ]) |]);
     ("Tree", [| ("Leaf", []); ("Node", [ TData 1; TInt; TData 1 ]) |]) |]

type mode = Borrow | Take

(* a body is a chain of lets and matches that ends in a simple expression *)
type simple =
  | Var of string
  | Int of int
  | Add of simple * simple
  | Con of int * int * simple list            (* type, constructor, fields *)
  | Call of int * simple list

type tail =
  | Simple of simple
  | Let of string * simple * tail
  | Match of string * int * (string list * tail) array   (* one arm for each constructor *)

type fn = { name : string; params : (string * ty * mode) list; ret : ty; body : tail }

(* ---------- reference semantics ---------- *)

type value = VI of int | VC of int * int * value list

exception Too_long

let steps = ref 0
let limit = ref 200_000
let tick () = incr steps; if !steps > !limit then raise Too_long

let rec ref_simple (fns : fn array) env = function
  | Var x -> List.assoc x env
  | Int n -> VI n
  | Add (a, b) -> (match ref_simple fns env a, ref_simple fns env b with VI x, VI y -> VI ((x + y) land 0xFFFF) | _ -> assert false)
  | Con (t, c, args) -> VC (t, c, List.map (ref_simple fns env) args)
  | Call (f, args) -> ref_call fns f (List.map (ref_simple fns env) args)

and ref_tail fns env = function
  | Simple s -> ref_simple fns env s
  | Let (x, s, body) -> let v = ref_simple fns env s in ref_tail fns ((x, v) :: env) body
  | Match (x, _, arms) -> (
      match List.assoc x env with
      | VC (_, c, fields) -> let binders, body = arms.(c) in ref_tail fns (List.combine binders fields @ env) body
      | VI _ -> assert false)

and ref_call fns f args =
  tick ();
  let fn = fns.(f) in
  ref_tail fns (List.map2 (fun (p, _, _) v -> (p, v)) fn.params args) fn.body

(* ---------- the counted form ---------- *)

type rhs =
  | RInt of int
  | RAdd of string * string
  | RCon of int * int * string list * string option   (* fields; the token that may hold its cell *)
  | RCall of int * string list

type code =
  | Ret of string
  | LetC of string * rhs * code
  | MatchC of string * int * (string list * code) array
  | Dup of string * code
  | Drop of string * code
  (* takes the matched cell apart: its fields go to the binders, moved if nothing else holds the
     cell and duplicated otherwise; with a token, an unshared cell is kept for a constructor *)
  | Open of string * string list * string option * code
  | FreeTok of string * code
  (* a turn of a destination-passing loop: the constructor with a hole at an index, then the
     arguments of the next turn *)
  | TailCons of int * int * string list * int * string option * string list
  | TailCall of string list

let counter = ref 0
let fresh p = incr counter; Printf.sprintf "%s%d" p !counter

(* normal form: every operand a variable *)
let rec norm_simple (s : simple) (k : string -> code) : code =
  match s with
  | Var x -> k x
  | Int n -> let t = fresh "t" in LetC (t, RInt n, k t)
  | Add (a, b) -> norm_simple a (fun x -> norm_simple b (fun y -> let t = fresh "t" in LetC (t, RAdd (x, y), k t)))
  | Con (ty, c, args) -> norm_list args (fun xs -> let t = fresh "t" in LetC (t, RCon (ty, c, xs, None), k t))
  | Call (f, args) -> norm_list args (fun xs -> let t = fresh "t" in LetC (t, RCall (f, xs), k t))

and norm_list (args : simple list) (k : string list -> code) : code =
  match args with
  | [] -> k []
  | a :: rest -> norm_simple a (fun x -> norm_list rest (fun xs -> k (x :: xs)))

(* `let x = y` would give two names to one reference; a let of a variable renames instead *)
let rec rename a b (e : tail) : tail =
  let rec rs = function
    | Var x -> Var (if x = a then b else x)
    | Int n -> Int n
    | Add (x, y) -> Add (rs x, rs y)
    | Con (t, c, xs) -> Con (t, c, List.map rs xs)
    | Call (f, xs) -> Call (f, List.map rs xs) in
  match e with
  | Simple s -> Simple (rs s)
  | Let (x, s, body) -> Let (x, rs s, rename a b body)
  | Match (x, t, arms) -> Match ((if x = a then b else x), t, Array.map (fun (bs, body) -> (bs, rename a b body)) arms)

let rec norm_tail (e : tail) : code =
  match e with
  | Simple s -> norm_simple s (fun x -> Ret x)
  | Let (x, Var y, body) -> norm_tail (rename x y body)
  | Let (x, s, body) -> norm_simple s (fun t -> norm_tail (rename x t body))
  | Match (x, t, arms) -> MatchC (x, t, Array.map (fun (bs, body) -> (bs, norm_tail body)) arms)

module S = Set.Make (String)

let rhs_vars = function
  | RInt _ -> []
  | RAdd (a, b) -> [ a; b ]
  | RCon (_, _, xs, _) -> xs
  | RCall (_, xs) -> xs

let rec fv (e : code) : S.t =
  match e with
  | Ret x -> S.singleton x
  | LetC (y, r, body) -> S.union (S.of_list (rhs_vars r)) (S.remove y (fv body))
  | MatchC (x, _, arms) -> Array.fold_left (fun acc (bs, body) -> S.union acc (S.diff (fv body) (S.of_list bs))) (S.singleton x) arms
  | Dup (x, k) | Drop (x, k) -> S.add x (fv k)
  | Open (x, bs, _, k) -> S.add x (S.diff (fv k) (S.of_list bs))
  | FreeTok (_, k) -> fv k
  | TailCons (_, _, xs, _, _, args) -> S.of_list (xs @ args)
  | TailCall args -> S.of_list args

(* faults that can be put into the passes, to see that the test finds them *)
let fault = ref ""

(* ---------- inserting count updates (section 9.2) ---------- *)

(* [owned]: variables whose one reference this code must hand on or release. Every other variable
   is borrowed: a read-only parameter, or what a match on one bound. *)
let rec insert (fns : fn array) (owned : S.t) (e : code) : code =
  let drops (xs : S.t) (k : code) = S.fold (fun x k -> Drop (x, k)) xs k in
  match e with
  | Ret x ->
      if S.mem x owned then drops (if !fault = "no-drop" then S.empty else S.remove x owned) (Ret x)
      else if !fault = "no-dup" then drops owned (Ret x)
      else Dup (x, drops owned (Ret x))
  | LetC (y, r, body) ->
      let after = S.remove y (fv body) in
      let args = rhs_vars r in
      let consuming =
        match r with
        | RCon _ -> List.map (fun _ -> true) args
        | RCall (f, _) -> List.map (fun (_, _, m) -> m = Take) fns.(f).params
        | RInt _ | RAdd _ -> List.map (fun _ -> false) args in
      (* an argument moves when this is the last the code has to do with its variable: it is not
         used after the let, not handed on again by a later argument, and not read by this same
         call, which must find it alive for as long as it runs *)
      let read = List.filter_map (fun (x, c) -> if c then None else Some x) (List.combine args consuming) in
      let rec go owned dups = function
        | [] -> (owned, dups)
        | (x, false) :: rest -> go owned dups rest
        | (x, true) :: rest ->
            let later = S.mem x after || List.exists (fun (z, c) -> c && z = x) rest || List.mem x read in
            if S.mem x owned && not later then go (S.remove x owned) dups rest
            else go owned (x :: dups) rest in
      let owned, dups = go owned [] (List.combine args consuming) in
      let owned = S.add y owned in
      (* what is owned and has no use left is released as soon as the let has run *)
      let dead = S.diff owned (fv body) in
      let body = insert fns (S.diff owned dead) body in
      List.fold_left (fun k x -> Dup (x, k)) (LetC (y, r, drops dead body)) dups
  | MatchC (x, t, arms) ->
      MatchC (x, t, Array.map (fun (bs, body) ->
          let live = fv body in
          (bs,
          if not (S.mem x owned) then
            (* borrowed: its fields are read where they are *)
            let dead = S.diff owned live in
            drops dead (insert fns (S.diff owned dead) body)
          else if S.mem x live then begin
            (* still needed: the fields used get references of their own *)
            let used = List.filter (fun b -> S.mem b live) bs in
            let owned = S.union owned (S.of_list used) in
            let dead = S.diff owned live in
            List.fold_left (fun k b -> Dup (b, k)) (drops dead (insert fns (S.diff owned dead) body)) used
          end else begin
            (* its last use: the cell is taken apart, and the fields are owned *)
            let owned = S.union (S.remove x owned) (S.of_list bs) in
            let dead = S.diff owned live in
            Open (x, bs, None, drops dead (insert fns (S.diff owned dead) body))
          end)) arms)
  | _ -> assert false

(* ---------- reuse (section 9.3) ---------- *)

(* offers the token to the first constructor of the same size on each path, and frees it on a
   path that has none *)
let rec offer (t : string) (size : int) (e : code) : code =
  match e with
  | LetC (y, RCon (ty, c, xs, None), body) when List.length xs = size -> LetC (y, RCon (ty, c, xs, Some t), body)
  | LetC (y, r, body) -> LetC (y, r, offer t size body)
  | Dup (x, k) -> Dup (x, offer t size k)
  | Drop (x, k) -> Drop (x, offer t size k)
  | Open (x, bs, tok, k) -> Open (x, bs, tok, offer t size k)
  | FreeTok (u, k) -> FreeTok (u, offer t size k)
  | MatchC (x, ty, arms) -> MatchC (x, ty, Array.map (fun (bs, body) -> (bs, offer t size body)) arms)
  | Ret x -> FreeTok (t, Ret x)
  | TailCons _ | TailCall _ -> assert false

let rec reuse (e : code) : code =
  match e with
  | Open (x, bs, None, k) when bs <> [] ->
      let t = fresh "tok" in
      Open (x, bs, Some t, reuse (offer t (List.length bs) k))
  | Open (x, bs, tok, k) -> Open (x, bs, tok, reuse k)
  | LetC (y, r, body) -> LetC (y, r, reuse body)
  | Dup (x, k) -> Dup (x, reuse k)
  | Drop (x, k) -> Drop (x, reuse k)
  | FreeTok (t, k) -> FreeTok (t, reuse k)
  | MatchC (x, ty, arms) -> MatchC (x, ty, Array.map (fun (bs, body) -> (bs, reuse body)) arms)
  | Ret _ | TailCons _ | TailCall _ -> e

(* ---------- destination passing (section 9.5) ---------- *)

(* A call of the function to itself whose result is one field of a constructor that is then
   returned, with nothing between the three, becomes a turn of a loop; so does a call of itself
   that is returned as it is. Returns the code and whether anything changed. *)
let dps (self : int) (e : code) : code * bool =
  let changed = ref false in
  let rec go e =
    match e with
    | LetC (r, RCall (f, args), LetC (c, RCon (ty, ctor, xs, tok), Ret c'))
      when f = self && c = c' && List.length (List.filter (fun x -> x = r) xs) = 1 && not (List.mem r args) ->
        changed := true;
        let rec index i = function x :: rest -> if x = r then i else index (i + 1) rest | [] -> assert false in
        TailCons (ty, ctor, xs, index 0 xs, tok, args)
    | LetC (r, RCall (f, args), Ret r') when f = self && r = r' -> changed := true; TailCall args
    | LetC (y, r, body) -> LetC (y, r, go body)
    | Dup (x, k) -> Dup (x, go k)
    | Drop (x, k) -> Drop (x, go k)
    | Open (x, bs, tok, k) -> Open (x, bs, tok, go k)
    | FreeTok (t, k) -> FreeTok (t, go k)
    | MatchC (x, ty, arms) -> MatchC (x, ty, Array.map (fun (bs, body) -> (bs, go body)) arms)
    | Ret _ | TailCons _ | TailCall _ -> e in
  let e = go e in
  (e, !changed)

(* ---------- the machine ---------- *)

exception Broken of string

type v = I of int | P of int | Null | Tok of int

type cell = { tag : int * int; fields : v array; mutable rc : int }

type machine = { heap : (int, cell) Hashtbl.t; tokens : (int, cell) Hashtbl.t; mutable next : int }

let cell_of m a = match Hashtbl.find_opt m.heap a with Some c -> c | None -> raise (Broken "a released cell is used")

let dup m = function P a -> let c = cell_of m a in c.rc <- c.rc + 1 | _ -> ()

let drop m v =
  let work = ref [ v ] in
  while !work <> [] do
    match !work with
    | P a :: rest ->
        work := rest;
        let c = cell_of m a in
        c.rc <- c.rc - 1;
        if c.rc < 0 then raise (Broken "a count went below zero");
        if c.rc = 0 then begin
          Hashtbl.remove m.heap a;
          Array.iter (fun f -> work := f :: !work) c.fields
        end
    | _ :: rest -> work := rest
    | [] -> ()
  done

let alloc m tag fields =
  m.next <- m.next + 1;
  Hashtbl.replace m.heap m.next { tag; fields; rc = 1 };
  P m.next

(* how often the machine built a constructor in a cell it had taken apart, and went round a loop *)
let reused = ref 0 and turns = ref 0 and cons_turns = ref 0

type compiled = { cparams : string list; ccode : code; loop : bool }

type dst = Slot of v ref | Field of int * int

let rec run_call m (fns : compiled array) (f : int) (args : v list) : v =
  tick ();
  let fn = fns.(f) in
  let result = ref Null in
  let dst = ref (Slot result) in
  let store v = match !dst with Slot r -> r := v | Field (a, i) -> (cell_of m a).fields.(i) <- v in
  let rec turn args =
    let env = Hashtbl.create 16 in
    List.iter2 (fun p a -> Hashtbl.replace env p a) fn.cparams args;
    let get x = match Hashtbl.find_opt env x with Some v -> v | None -> raise (Broken ("unbound " ^ x)) in
    (* a constructor, in the cell of its token when that holds one *)
    let build ty ctor fields tok =
      match tok with
      | Some t -> (
          match get t with
          | Tok a ->
              let c = Hashtbl.find m.tokens a in
              Hashtbl.remove m.tokens a;
              Hashtbl.replace env t Null;
              (* The cell is the same memory, but the model gives it a new address: anything that
                 still pointed at the cell that was taken apart then points at a released one, and
                 using it is the error it should be. *)
              incr reused;
              alloc m (ty, ctor) fields
          | _ -> alloc m (ty, ctor) fields)
      | None -> alloc m (ty, ctor) fields in
    let rec exec (e : code) : [ `Done of v | `Again of v list ] =
      match e with
      | Ret x -> `Done (get x)
      | LetC (y, r, body) ->
          let value =
            match r with
            | RInt n -> I n
            | RAdd (a, b) -> (match get a, get b with I x, I y -> I ((x + y) land 0xFFFF) | _ -> raise (Broken "adding what is not a number"))
            | RCon (ty, ctor, xs, tok) -> build ty ctor (Array.of_list (List.map get xs)) tok
            | RCall (g, xs) -> run_call m fns g (List.map get xs) in
          Hashtbl.replace env y value;
          exec body
      | MatchC (x, _, arms) -> (
          match get x with
          | P a ->
              let c = cell_of m a in
              let bs, body = arms.(snd c.tag) in
              List.iteri (fun i b -> Hashtbl.replace env b c.fields.(i)) bs;
              exec body
          | _ -> raise (Broken "a match on what is not a cell"))
      | Dup (x, k) -> dup m (get x); exec k
      | Drop (x, k) -> drop m (get x); exec k
      | Open (x, bs, tok, k) -> (
          match get x with
          | P a ->
              let c = cell_of m a in
              if c.rc = 1 || !fault = "reuse-shared" then begin
                (* nothing else holds it: the fields move out, and the cell is free *)
                Hashtbl.remove m.heap a;
                (match tok with
                 | Some t -> Hashtbl.replace m.tokens a c; Hashtbl.replace env t (Tok a)
                 | None -> ())
              end else begin
                Array.iter (dup m) c.fields;
                c.rc <- c.rc - 1;
                Option.iter (fun t -> Hashtbl.replace env t Null) tok
              end;
              exec k
          | _ -> raise (Broken "taking apart what is not a cell"))
      | FreeTok (t, k) ->
          (match get t with Tok a -> Hashtbl.remove m.tokens a; Hashtbl.replace env t Null | _ -> ());
          exec k
      | TailCons (ty, ctor, xs, hole, tok, args) ->
          let next = List.map get args in
          let fields = Array.of_list (List.mapi (fun i x -> if i = hole then Null else get x) xs) in
          let cell = build ty ctor fields tok in
          store cell;
          incr cons_turns;
          (match cell with P a -> dst := Field (a, if !fault = "wrong-hole" then (hole + 1) mod Array.length fields else hole) | _ -> assert false);
          `Again next
      | TailCall args -> `Again (List.map get args) in
    match exec fn.ccode with
    | `Done v -> if fn.loop then (store v; !result) else v
    | `Again next -> tick (); incr turns; turn next in
  turn args

let rec reify m (v : v) : value =
  match v with
  | I n -> VI n
  | P a -> let c = cell_of m a in VC (fst c.tag, snd c.tag, List.map (reify m) (Array.to_list c.fields))
  | Null | Tok _ -> raise (Broken "a hole or a token in a value")

(* ---------- random programs ---------- *)

let rand = ref (Random.State.make [| 1 |])
let below n = Random.State.int !rand n
let pick xs = List.nth xs (below (List.length xs))

type gen_ctx = {
  fns : fn list;                       (* the functions that may be called *)
  self : (int * (string * ty * mode) list * ty) option;
  smaller : string list;               (* parts of the first parameter: what a call of itself may be given *)
}

let rec gen_simple (ctx : gen_ctx) (env : (string * ty) list) (t : ty) (fuel : int) : simple =
  let vars = List.filter_map (fun (x, u) -> if u = t then Some (Var x) else None) env in
  let calls =
    if fuel <= 0 then []
    else
      List.concat (List.mapi (fun i (f : fn) ->
          if f.ret = t then [ (fun () -> Call (i, List.map (fun (_, u, _) -> gen_simple ctx env u (fuel - 1)) f.params)) ] else []) ctx.fns)
      @ (match ctx.self with
         | Some (i, params, ret) when ret = t && ctx.smaller <> [] ->
             [ (fun () -> Call (i, Var (pick ctx.smaller) :: List.map (fun (_, u, _) -> gen_simple ctx env u (fuel - 1)) (List.tl params))) ]
         | _ -> []) in
  let fresh_value () =
    match t with
    | TInt -> if fuel > 0 && below 3 = 0 then Add (gen_simple ctx env TInt (fuel - 1), gen_simple ctx env TInt (fuel - 1)) else Int (below 10)
    | TData d ->
        let ctors = snd decls.(d) in
        let c = if fuel <= 0 then 0 else below (Array.length ctors) in
        Con (d, c, List.map (fun u -> gen_simple ctx env u (fuel - 1)) (snd ctors.(c))) in
  match below 10 with
  | n when n < 4 && vars <> [] -> pick vars
  | n when n < 7 && calls <> [] -> (pick calls) ()
  | _ -> fresh_value ()

(* main builds the values the functions are run on, so its expressions go deeper *)
let depth (ctx : gen_ctx) = if ctx.self = None then 5 else 2

let rec gen_tail (ctx : gen_ctx) (env : (string * ty) list) (t : ty) (fuel : int) : tail =
  let boxed = List.filter_map (fun (x, u) -> match u with TData d -> Some (x, d) | TInt -> None) env in
  (* The shape destination passing is for: a constructor of the result type, one of whose fields
     is a call of the function on a part of its first parameter. Made often where it can be, so
     that the loops are run and not only made. *)
  let loop_shaped =
    match ctx.self, t with
    | Some (i, params, ret), TData d when ret = t && ctx.smaller <> [] && below 3 > 0 ->
        let ctors = snd decls.(d) in
        let holding = List.filter (fun c -> List.mem t (snd ctors.(c))) (List.init (Array.length ctors) Fun.id) in
        (match holding with
         | [] -> None
         | _ ->
             let c = pick holding in
             let placed = ref false in
             let fields = List.map (fun u ->
                 if u = t && not !placed then begin
                   placed := true;
                   Call (i, Var (pick ctx.smaller) :: List.map (fun (_, pu, _) -> gen_simple ctx env pu 1) (List.tl params))
                 end else gen_simple ctx env u 1) (snd ctors.(c)) in
             Some (Simple (Con (d, c, fields))))
    | _ -> None in
  match loop_shaped with
  | Some e -> e
  | None ->
  match below 10 with
  | n when n < 4 && fuel > 0 && boxed <> [] ->
      let x, d = pick boxed in
      let first = match ctx.self with Some (_, (p, _, _) :: _, _) -> Some p | _ -> None in
      Match (x, d, Array.map (fun (_, fields) ->
          let bs = List.map (fun _ -> fresh "b") fields in
          (* a field of the first parameter, or of a part of it, is smaller than it *)
          let smaller =
            if Some x = first || List.mem x ctx.smaller then
              List.filter_map (fun (b, u) -> if Some u = (match ctx.self with Some (_, (_, pt, _) :: _, _) -> Some pt | _ -> None) then Some b else None) (List.combine bs fields)
            else [] in
          (bs, gen_tail { ctx with smaller = smaller @ ctx.smaller } (List.combine bs fields @ env) t (fuel - 1))) (snd decls.(d)))
  | n when n < 7 && fuel > 0 ->
      let u = if below 2 = 0 then TInt else TData (below (Array.length decls)) in
      let x = fresh "x" in
      Let (x, gen_simple ctx env u (depth ctx), gen_tail ctx ((x, u) :: env) t (fuel - 1))
  | _ -> Simple (gen_simple ctx env t (depth ctx))

let gen_program () : fn array =
  let fns = ref [] in
  for i = 0 to 1 + below 4 do
    let params =
      (fresh "p", TData (below (Array.length decls)), (if below 2 = 0 then Borrow else Take))
      :: List.init (below 3) (fun _ -> (fresh "p", (if below 2 = 0 then TInt else TData (below (Array.length decls))), (if below 2 = 0 then Borrow else Take))) in
    let ret = if below 3 = 0 then TInt else TData (below (Array.length decls)) in
    let ctx = { fns = List.rev !fns; self = Some (i, params, ret); smaller = [] } in
    (* most bodies start by taking the first parameter apart, as a function over a list does *)
    let env = List.map (fun (p, t, _) -> (p, t)) params in
    let body =
      let (p, pt, _) = List.hd params in
      if below 4 > 0 then
        let d = match pt with TData d -> d | TInt -> assert false in
        Match (p, d, Array.map (fun (_, fields) ->
            let bs = List.map (fun _ -> fresh "b") fields in
            let smaller = List.filter_map (fun (b, u) -> if u = pt then Some b else None) (List.combine bs fields) in
            (bs, gen_tail { ctx with smaller } (List.combine bs fields @ env) ret 3)) (snd decls.(d)))
      else gen_tail ctx env ret 3 in
    fns := { name = Printf.sprintf "f%d" i; params; ret; body } :: !fns
  done;
  let callable = List.rev !fns in
  let ret = if below 2 = 0 then TInt else TData (below (Array.length decls)) in
  let main = { name = "main"; params = []; ret; body = gen_tail { fns = callable; self = None; smaller = [] } [] ret 5 } in
  Array.of_list (callable @ [ main ])

(* ---------- printing, for a program that fails ---------- *)

let rec show_simple = function
  | Var x -> x
  | Int n -> string_of_int n
  | Add (a, b) -> Printf.sprintf "(%s + %s)" (show_simple a) (show_simple b)
  | Con (t, c, []) -> fst (snd decls.(t)).(c)
  | Con (t, c, xs) -> Printf.sprintf "%s(%s)" (fst (snd decls.(t)).(c)) (String.concat ", " (List.map show_simple xs))
  | Call (f, xs) -> Printf.sprintf "f%d(%s)" f (String.concat ", " (List.map show_simple xs))

let rec show_tail ind = function
  | Simple s -> ind ^ show_simple s ^ "\n"
  | Let (x, s, body) -> Printf.sprintf "%slet %s = %s\n%s" ind x (show_simple s) (show_tail ind body)
  | Match (x, t, arms) ->
      Printf.sprintf "%smatch %s:\n%s" ind x
        (String.concat "" (Array.to_list (Array.mapi (fun c (bs, body) ->
             Printf.sprintf "%s  %s(%s) ->\n%s" ind (fst (snd decls.(t)).(c)) (String.concat ", " bs) (show_tail (ind ^ "    ") body)) arms)))

let show_program (fns : fn array) =
  String.concat "\n" (Array.to_list (Array.map (fun (f : fn) ->
      Printf.sprintf "fn %s(%s):\n%s" f.name
        (String.concat ", " (List.map (fun (p, _, m) -> (if m = Take then "take " else "") ^ p) f.params)) (show_tail "  " f.body)) fns))

let rec show_value = function
  | VI n -> string_of_int n
  | VC (t, c, []) -> fst (snd decls.(t)).(c)
  | VC (t, c, xs) -> Printf.sprintf "%s(%s)" (fst (snd decls.(t)).(c)) (String.concat ", " (List.map show_value xs))

(* ---------- the properties ---------- *)

type stage = Counted | Reused | Looped

let compile (stage : stage) (fns : fn array) : compiled array * int =
  let loops = ref 0 in
  let out = Array.mapi (fun i (f : fn) ->
      let owned = S.of_list (List.filter_map (fun (p, _, m) -> if m = Take then Some p else None) f.params) in
      let code = insert fns owned (norm_tail f.body) in
      let code = if stage = Counted then code else reuse code in
      let code, loop = if stage = Looped then dps i code else (code, false) in
      if loop then incr loops;
      { cparams = List.map (fun (p, _, _) -> p) f.params; ccode = code; loop }) fns in
  (out, !loops)

(* None when both properties hold for the program at this stage, Some why when one does not *)
let check (stage : stage) (fns : fn array) (expected : value) : string option * int =
  let compiled, loops = compile stage fns in
  let m = { heap = Hashtbl.create 64; tokens = Hashtbl.create 8; next = 0 } in
  steps := 0;
  limit := 800_000;
  let outcome =
    match run_call m compiled (Array.length fns - 1) [] with
    | exception Broken why -> Some ("P1: " ^ why)
    (* the reference semantics finished within the limit of steps, and the counted program makes
       the same calls: not finishing within several times that limit is a different meaning *)
    | exception Too_long -> Some "P2: the counted program does not finish where the reference semantics does"
    | result -> (
        match reify m result with
        | exception Broken why -> Some ("P1: " ^ why)
        | got ->
            if got <> expected then Some (Printf.sprintf "P2: the value is %s, and the reference semantics gives %s" (show_value got) (show_value expected))
            else begin
              match drop m result with
              | exception Broken why -> Some ("P1: " ^ why)
              | () ->
                  if Hashtbl.length m.heap <> 0 then Some (Printf.sprintf "P1: %d cells are never released" (Hashtbl.length m.heap))
                  else if Hashtbl.length m.tokens <> 0 then Some "P1: a cell kept for reuse is never used or freed"
                  else None
            end) in
  (outcome, loops)

let () =
  let count = ref 2000 and seed = ref 1 in
  let rec args = function
    | "--count" :: n :: rest -> count := int_of_string n; args rest
    | "--seed" :: n :: rest -> seed := int_of_string n; args rest
    | "--fault" :: f :: rest -> fault := f; args rest
    | [] -> ()
    | x :: _ -> Printf.eprintf "model: unknown argument %s\n" x; exit 2 in
  args (List.tl (Array.to_list Sys.argv));
  rand := Random.State.make [| !seed |];
  let ran = ref 0 and long = ref 0 and loops = ref 0 and cells = ref 0 in
  let made = ref 0 in
  while !ran < !count && !made < !count * 20 do
    incr made;
    counter := 0;
    let fns = gen_program () in
    steps := 0;
    limit := 200_000;
    match ref_call fns (Array.length fns - 1) [] with
    | exception Too_long -> incr long
    | exception Stack_overflow -> incr long
    | expected ->
        (* A value can share its parts, and be far larger written out than it was to build: one
           with more than a few thousand cells is set aside, like a program that ran too long. *)
        let budget = ref 5000 in
        let rec size = function
          | VI _ -> 0
          | VC (_, _, xs) -> decr budget; if !budget < 0 then raise Too_long; List.fold_left (fun a x -> a + size x) 1 xs in
        match size expected with
        | exception Too_long -> incr long
        | n ->
        incr ran;
        cells := !cells + n;
        List.iter (fun (stage, name) ->
            match check stage fns expected with
            | Some why, _ ->
                Printf.printf "FAIL %s (program %d of seed %d, %s)\n%s\n" why !made !seed name (show_program fns);
                exit 1
            | None, n -> if stage = Looped then loops := !loops + n)
          [ (Counted, "counting"); (Reused, "counting and reuse"); (Looped, "counting, reuse and destination passing") ]
  done;
  Printf.printf "%d programs: P1 and P2 hold with counting, with reuse, and with destination passing\n" !ran;
  Printf.printf "  %d cells in their results; %d constructors built in a cell taken apart; %d functions turned into loops, which went round %d times, %d of them by a constructor with a hole; %d programs set aside for running too long\n"
    !cells !reused !loops !turns !cons_turns !long
