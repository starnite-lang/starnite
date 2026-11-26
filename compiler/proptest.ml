(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Property tests (section 20.2): `test "name" for x: T, y: U where cond:`.

   Inputs are generated from their types: numbers, Bool, Char, Str, arrays, tuples, structs, data
   types, maps and sets. They start small and grow across the cases. A case that the `where`
   clause refuses is not counted; the test fails if fewer than one input in ten passes it. A
   failing case is shrunk before it is reported: numbers toward zero, strings and collections
   shorter, data toward its simpler variants. The seed is printed, and --seed runs it again.

   Not built: `where` clauses are only filters, never generators; failing cases are not saved
   under .stn/regressions; a type cannot implement Arbitrary by hand. *)

open Types
open Interp

exception No_generator of ty

(* a small generator of its own, so that a seed gives the same inputs on every machine and
   every version of OCaml *)
type rng = { mutable s : int64 }

let next r =
  (* splitmix64 *)
  r.s <- Int64.add r.s 0x9E3779B97F4A7C15L;
  let z = r.s in
  let z = Int64.mul (Int64.logxor z (Int64.shift_right_logical z 30)) 0xBF58476D1CE4E5B9L in
  let z = Int64.mul (Int64.logxor z (Int64.shift_right_logical z 27)) 0x94D049BB133111EBL in
  Int64.logxor z (Int64.shift_right_logical z 31)

(* a number in [0, n) *)
let below r n = if n <= 0 then 0 else Int64.to_int (Int64.unsigned_rem (next r) (Int64.of_int n))

let seed_of (name : string) (given : int option) : int =
  match given with
  | Some s -> s
  | None ->
      (* from the name of the test, by a hash written out here so that it is the same everywhere *)
      let h = ref 2166136261 in
      String.iter (fun c -> h := ((!h lxor Char.code c) * 16777619) land 0x3FFFFFFF) name;
      !h

let decl env n = Hashtbl.find_opt env.prog.decls n

(* Whether values of a type can be generated. A declared type met again while it is being looked
   at is taken on trust, or the question would not end: directly or through an array or another
   type, as in `type Tree = Leaf | Node(children: Array[Tree])`, and with other type arguments
   too, as in `type Nest[T] = End | Down(next: Nest[Array[T]])`, which never comes back to the
   same type twice. What the trust lets through, the generator still refuses when it gets there. *)
let generable env (t : ty) : bool =
  let rec go (seen : string list) (t : ty) =
    match repr t with
    | TInt _ | TFloat | TF32 | TBool | TChar | TStr | TUnit -> true
    | TArray e -> go seen e
    | TTuple ts -> List.for_all (go seen) ts
    | TNamed (("Map" | "Set"), args) -> List.for_all (go seen) args
    | TNamed (n, args) ->
        let key = n in
        List.mem key seen
        || (match decl env n with
            | Some { dbody = DStruct fs; dparams; _ } when List.length dparams = List.length args ->
                let s = List.combine dparams args in
                List.for_all (fun (f : field_info) -> go (key :: seen) (subst s f.fty)) fs
            | Some { dbody = DData vs; dparams; _ } when List.length dparams = List.length args ->
                let s = List.combine dparams args in
                List.for_all (fun (v : variant_info) -> List.for_all (fun (f : field_info) -> go (key :: seen) (subst s f.fty)) v.vfields) vs
            | _ -> false)
    | _ -> false in
  go [] t

(* Whether a type has a value that can be built at size 0 without building one of the declared
   types in [within], each with its type arguments, on the way: a number, an empty array, map or set, a struct of such fields,
   or a data type with a variant of such fields. A data type picks such a variant at size 0, so
   that generation ends, through other declarations too: `type First = More(next: Second) |
   End(value: Int)` with `type Second = Back(next: First)` ends with End. *)
let rec type_size (t : ty) : int =
  match repr t with
  | TArray e -> 1 + type_size e
  | TTuple ts | TNamed (_, ts) -> List.fold_left (fun n x -> n + type_size x) 1 ts
  | _ -> 1

(* a type on the way: the whole type as text, its declaration, and its size *)
type step = string * string * int

let rec finite env (within : step list) (t : ty) : bool =
  match repr t with
  | TArray _ | TNamed (("Map" | "Set"), _) -> true
  | TTuple ts -> List.for_all (finite env within) ts
  | TNamed (n, args) ->
      (* The types on the way are whole types, with their arguments: Layer[Int] inside
         Layer[Layer[Int]] is another type, and Done(Done(0)) a value. A way that comes back to a
         type it has passed goes nowhere. A type whose arguments grow at every step,
         Nest[Array[T]], is never met twice: that way is given up when one declaration stands on
         it sixteen times, each time at a larger type than before. Growth of that kind is the
         only bound. A long chain of declarations, a type nested deep in itself, whose steps get
         smaller, and a large type that a small one holds are all followed to their end. *)
      let key = show_ty (repr t) and size = type_size t in
      let rec grown count at_most = function
        | [] -> count
        | (_, d, sz) :: rest -> if d = n && sz < at_most then grown (count + 1) sz rest else grown count at_most rest in
      (not (List.exists (fun (k, _, _) -> k = key) within)) && grown 0 size within < 16
      && (match decl env n with
          | Some { dbody = DStruct fs; dparams; _ } when List.length dparams = List.length args ->
              let s = List.combine dparams args in
              List.for_all (fun (f : field_info) -> finite env ((key, n, size) :: within) (subst s f.fty)) fs
          | Some { dbody = DData vs; dparams; _ } when List.length dparams = List.length args ->
              let s = List.combine dparams args in
              List.exists (fun (v : variant_info) -> List.for_all (fun (f : field_info) -> finite env ((key, n, size) :: within) (subst s f.fty)) v.vfields) vs
          | _ -> true)
  | _ -> true

(* how deep a value being generated is: a type with no variant that ends, such as
   `type Ring = Link(next: Ring)`, has no values, and is given up on *)
let nesting = ref 0

(* The data types being given a value at size 0, outermost last. Each chose a variant because its
   fields could be built without coming back to the types already here; the fields are built under
   the same condition, so the choices agree all the way down. With `First = More(next: Second) |
   End(value: Int)` and `Second = Back(next: First) | Stop(value: Int)`, First may choose More
   because Second has Stop, and Second, built inside First, then has to choose Stop. *)
let ending : step list ref = ref []

let rec gen env (r : rng) (size : int) (t : ty) : value =
  incr nesting;
  if !nesting > 500 then raise (No_generator t);
  let v = gen_at env r size t in
  decr nesting;
  v

and gen_at env (r : rng) (size : int) (t : ty) : value =
  match repr t with
  | TUnit -> VUnit
  | TBool -> VBool (below r 2 = 1)
  | TInt k ->
      let lo = Values.min_of k and hi = Values.max_of k in
      let unsigned = not (ikind_signed k) in
      (* mostly within the size of the case, now and then at an end of the type's range *)
      (match below r 20 with
       | 0 -> VInt hi
       | 1 -> VInt lo
       | _ ->
           let n = Int64.of_int (below r (size + 1)) in
           let n = if (not unsigned) && below r 2 = 0 then Int64.neg n else n in
           VInt (if Values.fits k n then n else 0L))
  | TFloat | TF32 ->
      let whole = float_of_int (below r (size + 1)) and part = float_of_int (below r 4) /. 4.0 in
      VFloat (if below r 2 = 0 then whole +. part else -.(whole +. part))
  | TChar -> VChar (if below r 10 = 0 then [| 0xE9; 0x3BB; 0x4E2D; 0x1F600 |].(below r 4) else 32 + below r 95)
  | TStr ->
      let n = below r (size + 1) in
      let b = Buffer.create n in
      for _ = 1 to n do
        if below r 12 = 0 then Buffer.add_string b [| "\xC3\xA9"; "\xCE\xBB"; " "; "\n" |].(below r 4)
        else Buffer.add_char b (Char.chr (97 + below r 26))
      done;
      VStr (Buffer.contents b)
  | TArray e -> VArr (Array.init (below r (size + 1)) (fun _ -> gen env r size e))
  | TTuple ts -> VTuple (Array.of_list (List.map (gen env r size) ts))
  | TNamed ("Map", [ k; v ]) ->
      let es = ref [] in
      for _ = 1 to below r (size + 1) do
        let key = gen env r size k in
        if not (List.exists (fun (k', _) -> key_equal env k k' key) !es) then es := (key, gen env r size v) :: !es
      done;
      VMap (Array.of_list (List.rev !es))
  | TNamed ("Set", [ k ]) ->
      let ks = ref [] in
      for _ = 1 to below r (size + 1) do
        let key = gen env r size k in
        if not (List.exists (fun k' -> key_equal env k k' key) !ks) then ks := key :: !ks
      done;
      VSet (Array.of_list (List.rev !ks))
  | TNamed (n, args) -> (
      match decl env n with
      | Some { dbody = DStruct fs; dparams; _ } ->
          let s = List.combine dparams args in
          VStruct (Array.of_list (List.map (fun (f : field_info) -> gen env r size (subst s f.fty)) fs))
      | Some { dbody = DData vs; dparams; _ } ->
          let s = List.combine dparams args in
          (* At size 0, a variant that ends: one whose every field has a value that can be built
             without coming back to this type, and of those the one with the fewest fields.
             `Link(next: Chain) | End(value: Int)` ends with End, whichever is written first. *)
          let here : step = (show_ty (repr t), n, type_size t) in
          let ends (v : variant_info) = List.for_all (fun (f : field_info) -> finite env (here :: !ending) (subst s f.fty)) v.vfields in
          let shortest = function
            | [] -> None
            | first :: rest -> Some (List.fold_left (fun (best : variant_info) (v : variant_info) -> if List.length v.vfields < List.length best.vfields then v else best) first rest) in
          let fewest = match shortest (List.filter ends vs) with Some v -> v | None -> Option.get (shortest vs) in
          let v = if size <= 0 then fewest else List.nth vs (below r (List.length vs)) in
          let inner = if size <= 0 then 0 else size / 2 in
          (* what the fields are given at size 0 must end without this type, as the choice of
             this variant took for granted *)
          let saved = !ending in
          if size <= 0 then ending := here :: saved;
          let fields = List.map (fun (f : field_info) -> gen env r inner (subst s f.fty)) v.vfields in
          ending := saved;
          VVariant (v.vindex, Array.of_list fields)
      | _ -> raise (No_generator t))
  | _ -> raise (No_generator t)

(* simpler values to try in place of one that makes a test fail, the simplest first *)
let rec shrinks env (t : ty) (v : value) : value list =
  let each_slot (ts : ty list) (xs : value array) (make : value array -> value) =
    List.concat (List.mapi (fun i ti ->
        List.map (fun x -> let c = Array.copy xs in c.(i) <- x; make c) (shrinks env ti xs.(i))) ts) in
  let shorter xs =
    let n = Array.length xs in
    if n = 0 then []
    else
      [ [||]; Array.sub xs 0 (n / 2); Array.sub xs (n / 2) (n - n / 2) ]
      @ List.init (min n 8) (fun i -> Array.append (Array.sub xs 0 i) (Array.sub xs (i + 1) (n - i - 1)))
      |> List.filter (fun c -> Array.length c < n) in
  match repr t, v with
  | TInt _, VInt n ->
      if n = 0L then []
      else
        let half = Int64.div n 2L in
        let toward = if Int64.compare n 0L > 0 then Int64.sub n 1L else Int64.add n 1L in
        (* zero, then the same size without its sign, then nearer zero *)
        let plain = if Int64.compare n 0L < 0 && n <> Int64.min_int then [ Int64.neg n ] else [] in
        let rec uniq = function [] -> [] | x :: rest -> x :: uniq (List.filter (fun y -> y <> x) rest) in
        (* then smaller and smaller steps toward zero, down to one: a number that fails only
           above some bound is brought to that bound in a few dozen steps, not one at a time *)
        let steps = List.init 62 (fun k -> Int64.sub n (Int64.div n (Int64.shift_left 1L (k + 2)))) in
        uniq ([ 0L ] @ plain @ [ half ] @ steps @ [ toward ]) |> List.filter (fun x -> x <> n) |> List.map (fun x -> VInt x)
  | (TFloat | TF32), VFloat x -> if x = 0.0 then [] else List.filter (fun y -> y <> VFloat x) [ VFloat 0.0; VFloat (Float.trunc x); VFloat (x /. 2.0) ]
  | TBool, VBool true -> [ VBool false ]
  | TChar, VChar c -> if c = 97 then [] else [ VChar 97 ]
  | TStr, VStr s ->
      let n = String.length s in
      if n = 0 then []
      else
        (* cut where a character ends, so the text stays UTF-8 *)
        let starts = List.filter (fun i -> i = n || Char.code s.[i] land 0xC0 <> 0x80) (List.init (n + 1) Fun.id) in
        let cuts =
          [ ""; String.sub s 0 (List.fold_left (fun best i -> if i <= n / 2 then i else best) 0 starts) ]
          @ List.filter_map (fun i ->
                match List.find_opt (fun j -> j > i) starts with
                | Some j -> Some (String.sub s 0 i ^ String.sub s j (n - j))
                | None -> None) (List.filteri (fun k _ -> k < 8) (List.filter (fun i -> i < n) starts)) in
        List.sort_uniq compare (List.filter (fun c -> String.length c < n) cuts) |> List.map (fun c -> VStr c)
  | TArray e, VArr xs ->
      List.map (fun c -> VArr c) (shorter xs)
      @ List.concat (List.mapi (fun i x -> if i < 8 then List.map (fun y -> let c = Array.copy xs in c.(i) <- y; VArr c) (shrinks env e x) else []) (Array.to_list xs))
  | TTuple ts, VTuple xs -> each_slot ts xs (fun c -> VTuple c)
  | TNamed ("Map", _), VMap es -> List.map (fun c -> VMap c) (shorter es)
  | TNamed ("Set", _), VSet ks -> List.map (fun c -> VSet c) (shorter ks)
  | TNamed (n, args), VStruct xs -> (
      match decl env n with
      | Some { dbody = DStruct fs; dparams; _ } ->
          let s = List.combine dparams args in
          each_slot (List.map (fun (f : field_info) -> subst s f.fty) fs) xs (fun c -> VStruct c)
      | _ -> [])
  | TNamed (n, args), VVariant (i, xs) -> (
      match decl env n with
      | Some { dbody = DData vs; dparams; _ } ->
          let s = List.combine dparams args in
          let here = List.nth vs i in
          let fts = List.map (fun (f : field_info) -> subst s f.fty) here.vfields in
          (* a variant without fields; a field that is itself of this type; then each field simpler *)
          let bare = List.filter_map (fun (v : variant_info) -> if v.vfields = [] && v.vindex <> i then Some (VVariant (v.vindex, [||])) else None) vs in
          let inner = List.concat (List.mapi (fun j ft -> if ty_equal (repr ft) (repr t) then [ xs.(j) ] else []) fts) in
          bare @ inner @ each_slot fts xs (fun c -> VVariant (i, c))
      | _ -> [])
  | _ -> []

(* An input as it could be written in the program. Show is not used: a type need not have it,
   and a string is clearer in its quotes. *)
let rec show env (t : ty) (v : value) : string =
  let list ts xs = String.concat ", " (List.mapi (fun i ti -> show env ti xs.(i)) ts) in
  match repr t, v with
  | TStr, VStr s -> "\"" ^ String.escaped s ^ "\""
  | TArray e, VArr xs -> "[" ^ String.concat ", " (List.map (show env e) (Array.to_list xs)) ^ "]"
  | TTuple ts, VTuple xs -> "(" ^ list ts xs ^ ")"
  | TNamed ("Map", [ k; e ]), VMap es -> "{" ^ String.concat ", " (List.map (fun (a, b) -> show env k a ^ ": " ^ show env e b) (Array.to_list es)) ^ "}"
  | TNamed ("Set", [ k ]), VSet ks -> "{" ^ String.concat ", " (List.map (show env k) (Array.to_list ks)) ^ "}"
  | TNamed (n, args), VStruct xs -> (
      match decl env n with
      | Some { dbody = DStruct fs; dparams; _ } ->
          let s = List.combine dparams args in
          n ^ "(" ^ list (List.map (fun (f : field_info) -> subst s f.fty) fs) xs ^ ")"
      | _ -> show_value env t v)
  | TNamed (n, args), VVariant (i, xs) -> (
      match decl env n with
      | Some { dbody = DData vs; dparams; _ } ->
          let s = List.combine dparams args in
          let here = List.nth vs i in
          if here.vfields = [] then here.vname_
          else here.vname_ ^ "(" ^ list (List.map (fun (f : field_info) -> subst s f.fty) here.vfields) xs ^ ")"
      | _ -> show_value env t v)
  | _ -> show_value env t v

type outcome =
  | Passed of int                                  (* cases run *)
  | Too_few of int * int                           (* valid, generated *)
  | Failed_case of string * string list * int      (* what went wrong, the inputs as text, the seed *)
  | Cannot of ty

(* Runs one property. [run] binds the inputs and runs the body: None when it passes, Some why when
   it fails; [valid] is the where clause. *)
let check env ~(cases : int) ~(seed : int) (params : var list)
    ~(valid : value list -> bool) ~(run : value list -> string option) : outcome =
  match List.find_opt (fun (v : var) -> not (generable env v.vty)) params with
  | Some v -> Cannot v.vty
  | None -> try
      let r = { s = Int64.of_int seed } in
      let ran = ref 0 and made = ref 0 and failure = ref None in
      (* up to ten inputs are made for each case wanted, which is where "one in ten" is counted *)
      while !failure = None && !ran < cases && !made < cases * 10 do
        (* by inputs made, not cases run: a where clause that small inputs cannot pass is then given larger ones *)
        let size = min 40 (!made * 40 / max 1 cases) in
        nesting := 0;
        ending := [];
        let inputs = List.map (fun (v : var) -> gen env r size v.vty) params in
        incr made;
        if valid inputs then begin
          incr ran;
          match run inputs with
          | Some why -> failure := Some (why, inputs)
          | None -> ()
        end
      done;
      match !failure with
      | None -> if !ran < cases && !ran * 10 < !made then Too_few (!ran, !made) else Passed !ran
      | Some (why, inputs) ->
          (* take the first simpler input that is still valid and still fails, until none is *)
          let why = ref why and inputs = ref (Array.of_list inputs) in
          let tys = Array.of_list (List.map (fun (v : var) -> v.vty) params) in
          let steps = ref 0 and progress = ref true in
          while !progress && !steps < 1000 do
            progress := false;
            Array.iteri (fun i t ->
                if not !progress then
                  List.iter (fun candidate ->
                      if not !progress then begin
                        let trial = Array.copy !inputs in
                        trial.(i) <- candidate;
                        let l = Array.to_list trial in
                        if valid l then
                          match run l with
                          | Some w -> inputs := trial; why := w; progress := true; incr steps
                          | None -> ()
                      end) (shrinks env t !inputs.(i))) tys
          done;
          let shown = List.mapi (fun i (v : var) -> Printf.sprintf "%s = %s" v.vname (show env v.vty !inputs.(i))) params in
          Failed_case (!why, shown, seed)
    with No_generator t -> Cannot t
