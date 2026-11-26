(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Program fuzzer (section 21.2). Its programs use trait values (any Fig, any Chk, any
   Show): boxing, calls through method tables, arrays and nested values of them, closures
   that capture them, mut parameters and failures that cross a trait method.

   Builds well-typed programs by construction: it picks a type, then a production that
   yields that type, tracking which variables are live and mutable. Each program runs
   on the reference interpreter and on the debug C build; the outputs and exit
   statuses must match, and the debug runtime must report balanced counts.

   Negative fuzzing: a program that agrees gets one mutation with a known violation of a
   rule of the language, and the checker must reject it with the code of that rule.

   Half of the programs are split across a module (see [render]), and then also run as the
   one file that their text is.

   The compiler does not crash: with --crash, the bytes of each program are changed with
   no regard for what it says, and whatever the compiler says of the result, it must say.

   A failing program is shrunk, by taking out statements and items and simplifying what
   is left, while it still fails the same way.

     dune exec tests/fuzz/fuzz.exe -- [--count N] [--seed S] [--keep DIR] [--shrink]
     dune exec tests/fuzz/fuzz.exe -- --crash [--count N] [--seed S] [--keep DIR] [--shrink]
     dune exec tests/fuzz/fuzz.exe -- --reduce FILE [--keeping TEXT | --rejected CODE]

   tests/fuzz/selftest.sh checks the fuzzer itself, with the compilers of buggy.sh.
*)

let sprintf = Printf.sprintf

let types = [| "Int"; "Bool"; "Str"; "Array[Int]"; "Pair"; "Shape"; "Int?"; "any Show"; "Array[any Show]"; "Map[Str, Int]"; "Set[Int]" |]

(* Trait values have no Show of their own, so they are never printed directly: [types]
   are the printable ones, [all_types] also hold variables and parameters. *)
let any_types = [| "any Fig"; "Array[any Fig]"; "(any Fig)?"; "any Chk" |]
let all_types = Array.append types any_types

let prelude =
  {|fn no_int() -> Int?:
    None

fn no_ints() -> Array[Int]:
    []

fn no_counts() -> Map[Str, Int]:
    {}

fn no_keys() -> Set[Int]:
    {}

fn counts_of(xs: Array[Int]) -> Map[Str, Int]:
    var m: Map[Str, Int] = {}
    for x in xs:
        m[f"n{x % 3}"] += 1
    m

type Pair = struct(a: Int, b: Str)
type Shape = Dot | Box(w: Int, h: Int) | Named(name: Str, inner: Array[Int])

fn pair_a(mut p: Pair) -> lend mut Int:
    lend mut p.a

fn first_of(xs: Array[Int]) -> lend Int:
    lend xs[0]

fn slot(mut xs: Array[Int], i: Int) -> lend mut Int:
    lend mut xs[i]

fn either_end(mut xs: Array[Int], front: Bool) -> lend mut Int:
    if front:
        lend mut xs[0]
    else:
        lend mut xs[len(xs) - 1]

impl Show for Pair:
    fn show(p: Pair) -> Str:
        f"Pair({p.a}, {p.b})"

impl Show for Shape:
    fn show(s: Shape) -> Str:
        match s:
            Dot -> "Dot"
            Box(w, h) -> f"Box({w}, {h})"
            Named(n, xs) -> f"Named({n}, {xs})"

trait Fig:
    fn area(f: Self) -> Int
    fn label(f: Self) -> Str
    fn scale(f: Self, k: Int) -> Int

type Sq = struct(side: Int)
type Rc = struct(w: Int, h: Int)
type Tag = struct(name: Str, ns: Array[Int])
type Poly = Tri(a: Int) | Quad(a: Int, b: Int, c: Str) | Big(xs: Array[Int], ys: Array[Int], z: Str)
type Wrap = struct(inner: any Fig, k: Int)
type Many = struct(items: Array[any Fig], tag: Str)

impl Fig for Sq:
    fn area(f: Sq) -> Int:
        f.side *% f.side
    fn label(f: Sq) -> Str:
        f"sq{f.side}"
    fn scale(f: Sq, k: Int) -> Int:
        f.side *% k

impl Fig for Rc:
    fn area(f: Rc) -> Int:
        f.w *% f.h
    fn label(f: Rc) -> Str:
        f"rc{f.w}x{f.h}"
    fn scale(f: Rc, k: Int) -> Int:
        (f.w +% f.h) *% k

impl Fig for Tag:
    fn area(f: Tag) -> Int:
        len(f.name) +% len(f.ns)
    fn label(f: Tag) -> Str:
        f"tag{f.name}{f.ns}"
    fn scale(f: Tag, k: Int) -> Int:
        var t = k
        for n in f.ns:
            t = t +% n
        t

impl Fig for Poly:
    fn area(f: Poly) -> Int:
        match f:
            Tri(a) -> a
            Quad(a, b, c) -> (a *% b) +% len(c)
            Big(xs, ys, z) -> (len(xs) +% len(ys)) +% len(z)
    fn label(f: Poly) -> Str:
        match f:
            Tri(a) -> f"tri{a}"
            Quad(a, b, c) -> f"quad{a},{b},{c}"
            Big(xs, ys, z) -> f"big{xs}{ys}{z}"
    fn scale(f: Poly, k: Int) -> Int:
        match f:
            Tri(a) -> a *% k
            Quad(a, b, c) -> (a +% b) *% k
            Big(xs, ys, z) -> len(xs) *% k

impl Fig for Wrap:
    fn area(f: Wrap) -> Int:
        f.inner.area() +% f.k
    fn label(f: Wrap) -> Str:
        f"wrap({f.inner.label()},{f.k})"
    fn scale(f: Wrap, k: Int) -> Int:
        f.inner.scale(k) *% f.k

impl Fig for Many:
    fn area(f: Many) -> Int:
        var t = 0
        for x in f.items:
            t = t +% x.area()
        t
    fn label(f: Many) -> Str:
        var parts: Array[Str] = []
        for x in f.items:
            parts.push(x.label())
        f"{f.tag}[{join(parts, ",")}]"
    fn scale(f: Many, k: Int) -> Int:
        var t = 0
        for x in f.items:
            t = t +% x.scale(k)
        t

type Bad = Over(n: Int)

impl Show for Bad:
    fn show(e: Bad) -> Str:
        match e:
            Over(n) -> f"over{n}"

trait Chk:
    fn check(c: Self, limit: Int) -> Int ! Bad
    fn note(c: Self) -> Str

type Lim = struct(max: Int)
type Soft = struct(text: Str)

impl Chk for Lim:
    fn check(c: Lim, limit: Int) -> Int ! Bad:
        if limit > c.max:
            fail(Over(limit))
        limit
    fn note(c: Lim) -> Str:
        f"lim{c.max}"

impl Chk for Soft:
    fn check(c: Soft, limit: Int) -> Int:
        len(c.text) +% limit
    fn note(c: Soft) -> Str:
        c.text

fn describe(f: any Fig) -> Str:
    f"{f.label()}={f.area()}"

fn total(xs: Array[any Fig]) -> Int:
    var t = 0
    for x in xs:
        t = t +% x.area()
    t

fn total_gen[T: Fig](xs: Array[T]) -> Int:
    var t = 0
    for x in xs:
        t = t +% x.scale(2)
    t

fn via_any(f: any Fig, k: Int) -> Int:
    f.scale(k)

fn first_fig(xs: Array[any Fig]) -> any Fig:
    if len(xs) == 0:
        Sq(0)
    else:
        xs[0]

fn figs_from(xs: Array[Int]) -> Array[any Fig]:
    var r: Array[any Fig] = []
    for x in xs:
        if x % 2 == 0:
            r.push(Sq(x))
        else:
            r.push(Rc(x, 2))
    r

fn pair_figs(a: any Fig, b: any Fig) -> Array[any Fig]:
    [a, b]

fn no_fig() -> (any Fig)?:
    None

fn some_fig(f: any Fig) -> (any Fig)?:
    Some(f)

fn no_figs() -> Array[any Fig]:
    []

fn guard(c: any Chk, n: Int) -> Int:
    (try c.check(n)).or(-1)

fn shows_from(xs: Array[Int]) -> Array[any Show]:
    var r: Array[any Show] = []
    for x in xs:
        if x % 2 == 0:
            r.push(x)
        else:
            r.push(Pair(x, "s"))
    r

fn no_shows() -> Array[any Show]:
    []

fn show_gen[T: Show](x: T) -> Str:
    f"[{x}]"

fn call_it(f: fn() -> Int) -> Int:
    f()

fn grow(mut xs: Array[any Fig], f: any Fig):
    xs.push(f)

fn replace_fig(mut a: any Fig, b: any Fig):
    a = b

fn must_check(c: any Chk, n: Int) -> Int ! Bad:
    c.check(n)

fn eat(take s: Str) -> Int:
    len(s)

fn eat_ints(take xs: Array[Int]) -> Int:
    len(xs)

fn two_mut(mut a: Array[Int], mut b: Array[Int]):
    a.push(len(b))

fn with_cb(mut xs: Array[Int], f: fn() -> Int):
    xs.push(f())
|}

(* The text of a program is one file, with a comment line between the prelude and what is generated.
   When its first line is [module_header] the program is written as two files: a module with the
   prelude, all of it exported, and a main that imports it and writes each name of the module with
   the module's name before it (see [render]). The text is also the one-file program that the two
   stand for, and the two must do the same. *)
let generated_marker = "# generated"
let module_header = "# module"

(* A type of the program itself that implements a trait of the prelude, after main: when the prelude is in a
   module, the impl of a trait of one module for a type of another. *)
let local_block =
  {|type Local = struct(k: Int)

impl Fig for Local:
    fn area(f: Local) -> Int:
        f.k *% 3
    fn label(f: Local) -> Str:
        f"loc{f.k}"
    fn scale(f: Local, k: Int) -> Int:
        f.k +% k|}

(* ---------- the generator ---------- *)

type gen = {
  rng : Random.State.t;
  mutable scopes : (string * string * bool) list list;   (* name, type, mutable *)
  mutable n : int;
  mutable fns : (string * string list) list;              (* functions returning Int *)
  (* How many loops over an array the statements being made are inside. There, no array that is
     already in scope is made longer: a loop over an array that lengthens it, inside another such
     loop, multiplies its length at every turn, and the program does not finish in the time a run
     is given. A loop over a range has a fixed number of turns and is no such loop. *)
  mutable array_loops : int;
}

let int g k = Random.State.int g.rng k
let range g lo hi = lo + int g (hi - lo)        (* in [lo, hi) *)
let chance g p = Random.State.float g.rng 1.0 < p
let choice g a = a.(int g (Array.length a))
let choice_l g l = List.nth l (int g (List.length l))

let fresh g p = g.n <- g.n + 1; sprintf "%s%d" p g.n

let vars_of ?mutable_ g t =
  List.concat_map
    (List.filter_map (fun (n, ty, m) ->
         if ty = t && (match mutable_ with None -> true | Some want -> m = want) then Some n else None))
    g.scopes

let small g =
  if chance g 0.8 then string_of_int (range g (-5) 6)
  else choice g [| "2147483648"; "4611686018427387904"; "-1099511627776" |]

(* literals for the prefix, suffix and search shapes the compiler lowers to fixed-width loads: lengths
   around the 1, 2, 4 and 8 byte widths, and bytes of a multi-byte character *)
let short_lit g =
  choice g [| {|""|}; {|"a"|}; {|"bc"|}; {|"abc"|}; {|"0123"|}; {|"héllo"|}; {|"  name"|}; {|"  "|}; {|"01234567"|}; {|"012345678"|}; {|"é"|} |]

let four_byte_lit g = choice g [| {|"name"|}; {|"alph"|}; {|"bcde"|}; {|"abé"|}; {|"0123"|}; {|"cdef"|}; {|"f012"|}; {|"é漢"|} |]

let leaf g t =
  match t with
  | "Int" -> small g
  | "Bool" -> choice g [| "true"; "false" |]
  | "Str" -> choice g [| {|"a"|}; {|"bc"|}; {|""|}; {|"héllo"|}; {|"0123456789abcdef"|}; {|"  name1042,alpha,tag3126,é漢🙂  "|}; {|"0123456789abcdef0123456789abcdef!"|} |]
  | "Array[Int]" -> choice g [| "no_ints()"; "[1]"; "[3, 1, 2]" |]
  | "Map[Str, Int]" -> choice g [| "no_counts()"; {|{"a": 1}|}; {|{"b": 2, "a": -1, "b": 3}|} |]
  | "Set[Int]" -> choice g [| "no_keys()"; "{1}"; "{3, 1, 2, 3}" |]
  | "Pair" -> {|Pair(0, "p")|}
  | "Shape" -> "Dot"
  | "Int?" -> "no_int()"
  | "any Show" -> choice g [| "Pair(0, \"p\")"; "7"; "true"; "Dot" |]
  | "Array[any Show]" -> "no_shows()"
  | "any Fig" -> choice g [| "Sq(1)"; "Rc(2, 3)"; "Tri(4)"; "Local(5)" |]
  | "Array[any Fig]" -> "no_figs()"
  | "(any Fig)?" -> "no_fig()"
  | "any Chk" -> choice g [| "Lim(3)"; {|Soft("s")|} |]
  | _ -> invalid_arg t

let rec expr g t d =
  let vs = vars_of g t in
  if vs <> [] && chance g 0.45 then choice_l g vs
  else if d <= 0 then leaf g t
  else
    let e t' = expr g t' (d - 1) in
    match t with
    | "Int" -> (
        match int g 17 with
        | 0 -> sprintf "(%s +%% %s)" (e "Int") (e "Int")
        | 1 -> sprintf "(%s -%% %s)" (e "Int") (e "Int")
        | 2 -> sprintf "(%s *%% %s)" (e "Int") (small g)
        | 3 -> sprintf "len(%s)" (e "Array[Int]")
        | 4 -> sprintf "len(%s)" (e "Str")
        | 5 -> sprintf "(if %s: %s else: %s)" (e "Bool") (e "Int") (e "Int")
        | 6 -> sprintf "%s.a" (e "Pair")
        | 7 -> sprintf "(%s).or(%s)" (e "Int?") (small g)
        | 8 -> (
            match int g 3 with
            | 0 -> sprintf "len(%s)" (e "Map[Str, Int]")
            | 1 -> sprintf "len(%s)" (e "Set[Int]")
            | _ -> sprintf "(%s).get(%s).or(%s)" (e "Map[Str, Int]") (e "Str") (small g))
        | 9 -> sprintf "total(%s)" (e "Array[any Fig]")
        | 10 -> sprintf "via_any(%s, %s)" (e "any Fig") (e "Int")
        | 11 -> sprintf "total_gen(%s)" (e "Array[any Fig]")
        | 12 -> sprintf "guard(%s, %s)" (e "any Chk") (e "Int")
        | 13 -> sprintf "len(%s)" (e "Array[any Fig]")
        | 15 -> sprintf "call_it(fn(): %s)" (e "Int")
        | 14 -> (
            (* a call on a variable: the receiver is the trait value itself *)
            match vars_of g "any Fig" with
            | [] -> sprintf "via_any(%s, %s)" (e "any Fig") (e "Int")
            | vs -> sprintf "%s.area()" (choice_l g vs))
        | _ -> (
            match g.fns with
            | [] -> leaf g t
            | fns ->
                let name, ps = choice_l g fns in
                sprintf "%s(%s)" name (String.concat ", " (List.map e ps))))
    | "Bool" -> (
        match int g 13 with
        | 10 -> sprintf "(%s).contains(%s)" (e "Set[Int]") (e "Int")
        | 11 -> sprintf "contains(%s, %s)" (e "Map[Str, Int]") (e "Str")
        | 12 -> if chance g 0.5 then sprintf "(%s == %s)" (e "Set[Int]") (e "Set[Int]") else sprintf "(%s != %s)" (e "Map[Str, Int]") (e "Map[Str, Int]")
        | 0 -> sprintf "(%s < %s)" (e "Int") (e "Int")
        | 1 -> sprintf "(%s == %s)" (e "Str") (e "Str")
        | 2 -> sprintf "(%s and %s)" (e "Bool") (e "Bool")
        | 3 -> sprintf "(not %s)" (e "Bool")
        | 4 -> sprintf "(%s == %s)" (e "Array[Int]") (e "Array[Int]")
        | 5 -> sprintf "starts_with(%s, %s)" (e "Str") (short_lit g)
        | 6 -> sprintf "ends_with(%s, %s)" (e "Str") (short_lit g)
        | 7 -> sprintf "contains(%s, %s)" (e "Str") (four_byte_lit g)
        | 8 -> sprintf "contains(%s, %s)" (e "Str") (short_lit g)
        | _ -> sprintf "contains(%s, %s)" (e "Array[Int]") (e "Int"))
    | "Str" -> (
        match int g 9 with
        | 0 -> sprintf "(%s + %s)" (e "Str") (e "Str")
        | 1 -> sprintf {|f"<{%s}|{%s}>"|} (e "Int") (e (choice g types))
        | 2 -> sprintf "%s.b" (e "Pair")
        | 4 -> sprintf "describe(%s)" (e "any Fig")
        | 8 -> sprintf "show_gen(%s)" (e (choice g types))
        | 5 -> (
            match vars_of g "any Fig" with
            | [] -> sprintf "describe(%s)" (e "any Fig")
            | vs -> sprintf "%s.label()" (choice_l g vs))
        | 6 -> (
            match vars_of g "any Chk" with
            | [] -> {|"nochk"|}
            | vs -> sprintf "%s.note()" (choice_l g vs))
        | _ -> sprintf {|join(["x", %s], "-")|} (e "Str"))
    | "Array[Int]" -> (
        match int g 5 with
        | 4 -> sprintf "[%s; %d]" (e "Int") (int g 4)
        | 0 -> "[" ^ String.concat ", " (List.init (range g 1 4) (fun _ -> e "Int")) ^ "]"
        | 1 -> sprintf "[x +%% %s for x in %s]" (small g) (e "Array[Int]")
        | 2 -> sprintf "[i *%% i for i in 0..%d]" (int g 6)
        | _ -> sprintf "filled(%d, %s)" (int g 4) (e "Int"))
    | "Map[Str, Int]" -> (
        match int g 4 with
        | 0 -> "{" ^ String.concat ", " (List.init (range g 1 4) (fun _ -> sprintf "%s: %s" (e "Str") (e "Int"))) ^ "}"
        | 1 -> sprintf "{f\"k{x}\": x *%% 2 for x in %s}" (e "Array[Int]")
        | 2 -> sprintf "{k: v +%% 1 for (k, v) in %s if v > %s}" (e "Map[Str, Int]") (small g)
        | _ -> sprintf "counts_of(%s)" (e "Array[Int]"))
    | "Set[Int]" -> (
        match int g 6 with
        | 0 -> "{" ^ String.concat ", " (List.init (range g 1 4) (fun _ -> e "Int")) ^ "}"
        | 1 -> sprintf "(%s | %s)" (e "Set[Int]") (e "Set[Int]")
        | 2 -> sprintf "(%s & %s)" (e "Set[Int]") (e "Set[Int]")
        | 3 -> sprintf "(%s - %s)" (e "Set[Int]") (e "Set[Int]")
        | 4 -> sprintf "{x %% 5 for x in %s}" (e "Array[Int]")
        | _ -> sprintf "{v for (_, v) in %s}" (e "Map[Str, Int]"))
    | "Pair" -> sprintf "Pair(%s, %s)" (e "Int") (e "Str")
    | "Shape" -> (
        match int g 3 with
        | 0 -> "Dot"
        | 1 -> sprintf "Box(%s, %s)" (e "Int") (e "Int")
        | _ -> sprintf "Named(%s, %s)" (e "Str") (e "Array[Int]"))
    | "Int?" -> if chance g 0.6 then sprintf "Some(%s)" (e "Int") else "no_int()"
    | "any Show" ->
        (* any printable value: boxed where a trait value is expected *)
        e (choice g [| "Int"; "Str"; "Bool"; "Pair"; "Shape"; "Array[Int]"; "Int?" |])
    | "Array[any Show]" -> if chance g 0.7 then sprintf "shows_from(%s)" (e "Array[Int]") else "no_shows()"
    | "any Fig" -> (
        match int g 12 with
        | 0 -> sprintf "Sq(%s)" (e "Int")
        | 1 -> sprintf "Rc(%s, %s)" (e "Int") (e "Int")
        | 2 -> sprintf "Tag(%s, %s)" (e "Str") (e "Array[Int]")
        | 3 -> sprintf "Tri(%s)" (e "Int")
        | 4 -> sprintf "Quad(%s, %s, %s)" (e "Int") (e "Int") (e "Str")
        | 5 -> sprintf "Big(%s, %s, %s)" (e "Array[Int]") (e "Array[Int]") (e "Str")
        | 6 -> sprintf "Wrap(%s, %s)" (e "any Fig") (e "Int")
        | 7 -> sprintf "Many(%s, %s)" (e "Array[any Fig]") (e "Str")
        | 8 -> sprintf "first_fig(%s)" (e "Array[any Fig]")
        | 9 -> sprintf "(%s).or(%s)" (e "(any Fig)?") (e "any Fig")
        | 10 -> sprintf "Local(%s)" (e "Int")
        | _ -> leaf g t)
    | "Array[any Fig]" -> (
        match int g 3 with
        | 0 -> sprintf "figs_from(%s)" (e "Array[Int]")
        | 1 -> sprintf "pair_figs(%s, %s)" (e "any Fig") (e "any Fig")
        | _ -> leaf g t)
    | "(any Fig)?" -> if chance g 0.6 then sprintf "some_fig(%s)" (e "any Fig") else "no_fig()"
    | "any Chk" -> if chance g 0.5 then sprintf "Lim(%s)" (e "Int") else sprintf "Soft(%s)" (e "Str")
    | _ -> invalid_arg t

let with_scope g vars f =
  g.scopes <- g.scopes @ [ vars ];
  let r = f () in
  g.scopes <- List.rev (List.tl (List.rev g.scopes));
  r

let declare g v = match List.rev g.scopes with last :: rest -> g.scopes <- List.rev ((last @ [ v ]) :: rest) | [] -> ()

let rec stmts g ind k d = List.concat (List.init k (fun _ -> stmt g ind d))

and stmt g ind d =
  let p = String.make (4 * ind) ' ' in
  let k = int g 18 in
  let fallback () = [ sprintf "%sprint(%s)" p (leaf g "Str") ] in
  if k <= 1 || d <= 0 then begin
    let t = choice g all_types in
    let n = fresh g "v" in
    let mut = chance g 0.5 in
    let line = sprintf "%s%s %s: %s = %s" p (if mut then "var" else "let") n t (expr g t 3) in
    declare g (n, t, mut);
    [ line ]
  end
  else
    match k with
    | 2 -> (
        let t = choice g all_types in
        match vars_of ~mutable_:true g t with
        | [] -> fallback ()
        | vs -> [ sprintf "%s%s = %s" p (choice_l g vs) (expr g t 3) ])
    | 3 -> (
        match vars_of ~mutable_:true g "Array[Int]" with
        | [] -> fallback ()
        | vs -> (
            let v = choice_l g vs in
            match (if g.array_loops > 0 then 1 + int g 3 else int g 4) with
            | 0 -> [ sprintf "%s%s.push(%s)" p v (expr g "Int" 2) ]
            | 1 -> [ sprintf "%sif len(%s) > 0:" p v; sprintf "%s    %s[0] = %s" p v (expr g "Int" 2) ]
            | 2 -> [ sprintf "%ssort(mut %s)" p v ]
            | _ -> [ sprintf "%slet %s = %s.pop()" p (fresh g "v") v ]))
    | 4 -> [ sprintf "%sprint(%s)" p (expr g "Str" 3) ]
    | 5 -> [ sprintf {|%sprint(f"{%s}")|} p (expr g (choice g types) 3) ]
    | 6 ->
        let c = sprintf "%sif %s:" p (expr g "Bool" 2) in
        let a = with_scope g [] (fun () -> stmts g (ind + 1) (range g 1 3) (d - 1)) in
        let b = with_scope g [] (fun () -> stmts g (ind + 1) (range g 1 3) (d - 1)) in
        (c :: a) @ (sprintf "%selse:" p :: b)
    | 7 ->
        let n = fresh g "i" in
        let head = sprintf "%sfor %s in %s:" p n (expr g "Array[Int]" 2) in
        g.array_loops <- g.array_loops + 1;
        let body = with_scope g [ (n, "Int", false) ] (fun () -> stmts g (ind + 1) (range g 1 3) (d - 1)) in
        g.array_loops <- g.array_loops - 1;
        head :: body
    | 8 ->
        let head = sprintf "%smatch %s:" p (expr g "Shape" 2) in
        let arms =
          [ ("Dot", []); ("Box(w, h)", [ ("w", "Int"); ("h", "Int") ]);
            ("Named(nm, xs)", [ ("nm", "Str"); ("xs", "Array[Int]") ]) ]
        in
        head
        :: List.concat_map
             (fun (pat, binds) ->
               sprintf "%s    %s ->" p pat
               :: with_scope g (List.map (fun (b, t) -> (b, t, false)) binds) (fun () -> stmts g (ind + 2) 1 (d - 1)))
             arms
    | 9 -> (
        match vars_of ~mutable_:true g "Int" with
        | [] -> fallback ()
        | vs ->
            let v = choice_l g vs in
            [ sprintf "%svar %s = 0" p (fresh g "c"); sprintf "%swhile %s > 0 and %s < 50:" p v v;
              sprintf "%s    %s = %s +%% 7" p v v ])
    | 10 ->
        (* a loop over trait values: each is called through its method table *)
        let n = fresh g "f" in
        let head = sprintf "%sfor %s in %s:" p n (expr g "Array[any Fig]" 2) in
        g.array_loops <- g.array_loops + 1;
        let body =
          with_scope g [ (n, "any Fig", false) ] (fun () ->
               [ sprintf "%s    print(describe(%s))" p n; sprintf {|%s    print(f"{%s.scale(%s)}")|} p n (small g) ]
               @ stmts g (ind + 1) 1 (d - 1)) in
        g.array_loops <- g.array_loops - 1;
        head :: body
    | 11 ->
        let head = sprintf "%smatch %s:" p (expr g "(any Fig)?" 2) in
        let n = fresh g "f" in
        [ head; sprintf "%s    Some(%s) ->" p n ]
        @ with_scope g [ (n, "any Fig", false) ] (fun () ->
              [ sprintf "%s        print(%s.label())" p n ] @ stmts g (ind + 2) 1 (d - 1))
        @ [ sprintf "%s    None ->" p; sprintf {|%s        print("none")|} p ]
    | 12 -> (
        match vars_of ~mutable_:true g "Array[any Fig]" with
        | [] -> fallback ()
        | vs -> (
            let v = choice_l g vs in
            (* inside a loop over an array, only what leaves its length or shortens it *)
            match (if g.array_loops > 0 then (if chance g 0.5 then 1 else 4) else int g 5) with
            | 0 -> [ sprintf "%s%s.push(%s)" p v (expr g "any Fig" 2) ]
            | 1 -> [ sprintf "%sif len(%s) > 0:" p v; sprintf "%s    %s[0] = %s" p v (expr g "any Fig" 2) ]
            | 2 -> [ sprintf "%sfor %s in %s:" p (fresh g "f") (expr g "Array[any Fig]" 1); sprintf "%s    %s.push(%s)" p v (expr g "any Fig" 1) ]
            | 3 -> [ sprintf "%sgrow(mut %s, %s)" p v (expr g "any Fig" 2) ]
            | _ -> [ sprintf "%slet %s = %s.pop()" p (fresh g "v") v ]))
    | 13 when chance g 0.4 ->
        (* a failure that crosses a trait method and is caught here *)
        let n = fresh g "v" and e = fresh g "e" in
        [ sprintf "%smatch try must_check(%s, %s):" p (expr g "any Chk" 2) (expr g "Int" 2);
          sprintf "%s    Ok(%s) -> print(f\"ok {%s}\")" p n n;
          sprintf "%s    Err(%s) -> print(f\"{%s}\")" p e e ]
    | 13 -> (
        match vars_of ~mutable_:true g "any Fig" with
        | [] -> fallback ()
        | vs ->
            (* the new value is bound first: passing the variable itself would overlap the mut argument *)
            let t = fresh g "v" in
            let line = sprintf "%slet %s: any Fig = %s" p t (expr g "any Fig" 2) in
            declare g (t, "any Fig", false);
            [ line; sprintf "%sreplace_fig(mut %s, %s)" p (choice_l g vs) t ])
    | 17 -> (
        (* writes to a Map or a Set: an entry put, updated from the default, taken out; a key added or
           taken out; a loop over what the collection held when it started that writes to it *)
        match int g 2 with
        | 0 -> (
            match vars_of ~mutable_:true g "Map[Str, Int]" with
            | [] -> fallback ()
            | vs -> (
                let v = choice_l g vs in
                match int g 5 with
                | 0 -> [ sprintf "%s%s[%s] = %s" p v (expr g "Str" 1) (expr g "Int" 2) ]
                | 1 -> [ sprintf "%s%s[%s] += %s" p v (expr g "Str" 1) (small g) ]
                | 2 -> [ sprintf "%slet %s = %s.remove(%s)" p (fresh g "v") v (expr g "Str" 1) ]
                | 3 -> [ sprintf "%sfor (k, x) in %s:" p v; sprintf "%s    %s[k + \"!\"] = x +%% 1" p v ]
                | _ -> [ sprintf "%s%s.clear()" p v ]))
        | _ -> (
            match vars_of ~mutable_:true g "Set[Int]" with
            | [] -> fallback ()
            | vs -> (
                let v = choice_l g vs in
                match int g 4 with
                | 0 -> [ sprintf "%s%s.add(%s)" p v (expr g "Int" 2) ]
                | 1 -> [ sprintf "%slet %s = %s.remove(%s)" p (fresh g "v") v (expr g "Int" 1) ]
                | 2 -> [ sprintf "%sfor x in %s:" p v; sprintf "%s    %s.add(x *%% 3)" p v ]
                | _ -> [ sprintf "%s%s.clear()" p v ])))
    | 16 -> (
        (* projections (section 4.6): a write and a compound write through a lend mut call, on a field and on
           an element, a read through a lend call, and a function that lends one of two places. An index is
           bound first: the array is lent for the statement, so it cannot also be read in it (E0323) *)
        match int g 4 with
        | 0 -> (
            match vars_of ~mutable_:true g "Pair" with
            | [] -> fallback ()
            | vs ->
                let v = choice_l g vs in
                if chance g 0.5 then [ sprintf "%spair_a(mut %s) = %s" p v (small g) ]
                else [ sprintf "%spair_a(mut %s) += %s" p v (small g) ])
        | 1 -> (
            match vars_of ~mutable_:true g "Array[Int]" with
            | [] -> fallback ()
            | vs ->
                let v = choice_l g vs and i = fresh g "v" in
                [ sprintf "%sif len(%s) > 0:" p v;
                  sprintf "%s    let %s = len(%s) - 1" p i v;
                  sprintf "%s    slot(mut %s, %s) = %s" p v i (small g);
                  sprintf "%s    slot(mut %s, 0) += %s" p v (small g) ])
        | 2 -> (
            match vars_of g "Array[Int]" with
            | [] -> fallback ()
            | vs ->
                let v = choice_l g vs in
                [ sprintf "%sif len(%s) > 0:" p v; sprintf "%s    print(f\"{first_of(%s)}\")" p v ])
        | _ -> (
            match vars_of ~mutable_:true g "Array[Int]" with
            | [] -> fallback ()
            | vs ->
                let v = choice_l g vs and n = fresh g "v" in
                let line = sprintf "%slet %s = %s" p n v in
                declare g (n, "Array[Int]", false);
                (* a snapshot taken first keeps its elements when the lend writes *)
                [ line; sprintf "%sif len(%s) > 0:" p v; sprintf "%s    either_end(mut %s, %b) = %s" p v (chance g 0.5) (small g);
                  sprintf "%sprint(f\"{%s} {%s}\")" p n v ]))
    | 15 ->
        (* a counted loop that appends an affine integer to a local array: the shapes the compiler turns into
           one reservation and a fill, a bound that is empty or backwards, a base that overflows, an array that is
           shared when the loop starts, and the shapes beside it that it must leave alone *)
        let a, decl =
          match vars_of ~mutable_:true g "Array[Int]" with
          | vs when vs <> [] && g.array_loops = 0 && chance g 0.4 -> (choice_l g vs, [])
          | _ ->
              let a = fresh g "a" in
              let line = sprintf "%svar %s: Array[Int] = %s" p a (expr g "Array[Int]" 1) in
              declare g (a, "Array[Int]", true);
              (a, [ line ])
        in
        let lo = range g (-3) 4 in
        let hi = if chance g 0.2 then lo - range g 0 3 else lo + range g 0 40 in
        let base =
          if chance g 0.15 then choice g [| "9223372036854775800"; "-9223372036854775800"; "9223372036854775807" |]
          else expr g "Int" 1
        in
        let i = fresh g "i" in
        let loop pp body = [ sprintf "%sfor %s in %d..%d:" pp i lo hi; sprintf "%s    %s" pp body ] in
        let show = [ sprintf {|%sprint(f"{%s}")|} p a ] in
        decl
        @ (match int g 7 with
           | 0 -> loop p (sprintf "%s.push(%s + %s)" a base i)
           | 1 -> loop p (sprintf "%s.push(%s + %s)" a i base)
           | 2 -> loop p (sprintf "%s.push(%s - %s)" a base i)
           | 3 -> loop p (sprintf "%s.push(%s +%% %s)" a i base)
           | 4 ->
               let r = fresh g "r" in
               (sprintf "%sfor %s in 0..%d:" p r (range g 1 4) :: [ sprintf "%s    clear(mut %s)" p a ])
               @ loop (p ^ "    ") (sprintf "%s.push(%s + %s)" a i base)
           | 5 ->
               let snap = fresh g "s" in
               (sprintf "%slet %s: Array[Int] = %s" p snap a :: loop p (sprintf "%s.push(%s + %s)" a i base))
               @ [ sprintf {|%sprint(f"{%s}")|} p snap ]
           | _ -> loop p (sprintf "%s.push(%s + %s)" a i i))
        @ show
    | _ -> [ sprintf "%sprint(%s)" p (if chance g 0.5 then sprintf "describe(%s)" (expr g "any Fig" 2) else expr g "Str" 3) ]

let program seed =
  let g = { rng = Random.State.make [| seed |]; scopes = [ [] ]; n = 0; fns = []; array_loops = 0 } in
  let fns =
    List.init (int g 3) (fun _ ->
        let name = fresh g "f" in
        let ps = List.init (int g 3) (fun _ -> choice g [| "Int"; "Str"; "Array[Int]"; "any Fig"; "Array[any Fig]"; "any Chk" |]) in
        let saved = g.scopes in
        g.scopes <- [ List.mapi (fun i t -> (sprintf "p%d" i, t, false)) ps ];
        let body = stmts g 1 (int g 3) 1 in
        let ret = expr g "Int" 3 in
        g.scopes <- saved;
        g.fns <- g.fns @ [ (name, ps) ];
        (* the result is parenthesized: a line starting with '-' would continue the last one *)
        (sprintf "fn %s(%s) -> Int:" name (String.concat ", " (List.mapi (fun i t -> sprintf "p%d: %s" i t) ps)) :: body)
        @ [ sprintf "    (%s)" ret; "" ])
  in
  let main = stmts g 1 (range g 3 12) 3 in
  let text = String.concat "\n" ((prelude :: generated_marker :: List.concat fns) @ ("fn main():" :: main) @ [ {|    print("end")|}; ""; local_block ]) ^ "\n" in
  (* half of the programs are split across a module: see [render]. The generator's own random numbers are
     not used for it, so that a seed gives the same statements either way. *)
  if Random.State.bool (Random.State.make [| seed; 0x6d6f64 |]) then module_header ^ "\n" ^ text else text

(* ---------- text helpers ---------- *)

let lines_of text = Array.of_list (String.split_on_char '\n' text)
let text_of lines = String.concat "\n" (Array.to_list lines)

let indent_of s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && s.[!i] = ' ' do incr i done;
  !i

let blank l = String.trim l = ""

let is_prefix p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p

let contains s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  m = 0 || go 0

(* where the first occurrence of [sub] in [s] begins *)
let index_of s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = if i + m > n then None else if String.sub s i m = sub then Some i else go (i + 1) in
  go 0

(* the first occurrence of [sub] in [s], replaced *)
let replace_first s sub by =
  let n = String.length s and m = String.length sub in
  let rec find i = if i + m > n then None else if String.sub s i m = sub then Some i else find (i + 1) in
  match find 0 with Some i -> Some (String.sub s 0 i ^ by ^ String.sub s (i + m) (n - i - m)) | None -> None

let insert_after lines i news =
  Array.concat [ Array.sub lines 0 (i + 1); Array.of_list news; Array.sub lines (i + 1) (Array.length lines - i - 1) ]

(* a line, and the deeper lines under it; an if with its else goes together *)
let group_at lines i =
  let n = Array.length lines in
  let ind = indent_of lines.(i) in
  let after_body j =
    let j = ref j in
    while !j < n && (not (blank lines.(!j))) && indent_of lines.(!j) > ind do incr j done;
    !j
  in
  let j = after_body (i + 1) in
  if is_prefix "if " (String.trim lines.(i)) && j < n && indent_of lines.(j) = ind && String.trim lines.(j) = "else:" then after_body (j + 1)
  else j

let delete_lines lines i j = Array.append (Array.sub lines 0 i) (Array.sub lines j (Array.length lines - j))

(* ---------- programs in more than one file ---------- *)

let is_ident_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_ident_char c = is_ident_start c || (c >= '0' && c <= '9')

let split_str sep s =
  let m = String.length sep in
  let rec go from acc =
    match index_of (String.sub s from (String.length s - from)) sep with
    | Some i -> go (from + i + m) (String.sub s from i :: acc)
    | None -> List.rev (String.sub s from (String.length s - from) :: acc)
  in
  go 0 []

(* the line of the comment between the prelude and what is generated *)
let marker_index lines =
  let r = ref (-1) in
  Array.iteri (fun i l -> if l = generated_marker && !r < 0 then r := i) lines;
  !r

(* [single_file] is set by a reduction of a file that is not split: its candidates are written in that mode
   whatever they look like (they can come to look split, when what is before the header is taken out), so
   that a module that is next to the input is never written over.

   A text is a program split across a module when its first line is the header, exactly, and the line between
   the prelude and what is generated comes after it. A file that starts with a comment that begins alike
   (`# module smoke test`) is an ordinary program: the same test decides how a text is written and where a
   reduction is tried, so that what it imports is found where it is. *)
let single_file = ref false

let is_split text =
  let ls = lines_of text in
  (not !single_file) && Array.length ls > 0 && ls.(0) = module_header && marker_index ls > 0

(* a top-level function, type or trait, with a star after its name: the module exports it *)
let export_decl l =
  match List.find_opt (fun k -> is_prefix k l) [ "fn "; "type "; "trait " ] with
  | None -> l
  | Some k ->
      let j = ref (String.length k) in
      while !j < String.length l && is_ident_char l.[!j] do incr j done;
      String.sub l 0 !j ^ "*" ^ String.sub l !j (String.length l - !j)

(* the names a module has at its top level: functions, types, traits, and the variants of its data
   types, as the pieces of `A | B(x: Int) | C` after the equals sign *)
let top_names lines =
  let names = ref [] in
  let add s = if s <> "" && not (List.mem s !names) then names := s :: !names in
  let ident_at l j =
    let k = ref j in
    while !k < String.length l && is_ident_char l.[!k] do incr k done;
    String.sub l j (!k - j)
  in
  Array.iter
    (fun l ->
      List.iter
        (fun kw ->
          if is_prefix kw l then begin
            add (ident_at l (String.length kw));
            if kw = "type " then
              match index_of l " = " with
              | Some p ->
                  List.iter
                    (fun piece ->
                      let piece = String.trim piece in
                      if piece <> "" && piece.[0] >= 'A' && piece.[0] <= 'Z' then add (ident_at piece 0))
                    (split_str " | " (String.sub l (p + 3) (String.length l - p - 3)))
              | None -> ()
          end)
        [ "fn "; "type "; "trait " ])
    lines;
  !names

(* [text] with each of [names] that is not a member (after a dot) written with [modname] and a dot before it.
   String and character literals and comments are left as they are; the interpolations of an f-string are
   code, and may have string literals in them. *)
let qualify names modname text =
  let n = String.length text in
  let b = Buffer.create (n + (n / 8)) in
  let i = ref 0 in
  let copy () = Buffer.add_char b text.[!i]; incr i in
  let copy_literal q =
    copy ();
    while !i < n && text.[!i] <> q do
      if text.[!i] = '\\' && !i + 1 < n then copy ();
      copy ()
    done;
    if !i < n then copy ()
  in
  let after_dot () =
    let len = Buffer.length b in
    len >= 1 && Buffer.nth b (len - 1) = '.' && not (len >= 2 && Buffer.nth b (len - 2) = '.')
  in
  let rec code ~in_interpolation =
    let depth = ref 0 and fin = ref false in
    while (not !fin) && !i < n do
      let c = text.[!i] in
      if c = '"' || c = '\'' then copy_literal c
      else if c = '#' && not in_interpolation then (while !i < n && text.[!i] <> '\n' do copy () done)
      else if c = '{' then (incr depth; copy ())
      else if c = '}' then (if in_interpolation && !depth = 0 then fin := true else (decr depth; copy ()))
      else if is_ident_start c then begin
        let st = !i in
        while !i < n && is_ident_char text.[!i] do incr i done;
        let s = String.sub text st (!i - st) in
        if s = "f" && !i < n && text.[!i] = '"' then (Buffer.add_string b s; fstring ())
        else if (not (after_dot ())) && List.mem s names then (Buffer.add_string b modname; Buffer.add_char b '.'; Buffer.add_string b s)
        else Buffer.add_string b s
      end
      else if c >= '0' && c <= '9' then (while !i < n && is_ident_char text.[!i] do copy () done)
      else copy ()
    done
  and fstring () =
    copy ();
    while !i < n && text.[!i] <> '"' do
      if text.[!i] = '\\' && !i + 1 < n then (copy (); copy ())
      else if text.[!i] = '{' then begin
        copy ();
        code ~in_interpolation:true;
        if !i < n then copy ()
      end
      else copy ()
    done;
    if !i < n then copy ()
  in
  code ~in_interpolation:false;
  Buffer.contents b

let module_name = "fuzzlib"

(* the files a text stands for: its main, and the module that main imports, if it has one *)
type files = { main : string; lib : string option }

let render text =
  let lines = lines_of text in
  let k = marker_index lines in
  if is_split text && k > 0 then begin
    let lib_lines = Array.sub lines 1 (k - 1) in
    let rest = Array.sub lines (k + 1) (Array.length lines - k - 1) in
    { main = "import " ^ module_name ^ "\n\n" ^ qualify (top_names lib_lines) module_name (text_of rest);
      lib = Some (text_of (Array.map export_decl lib_lines)) }
  end
  else { main = text; lib = None }

(* write a program: [path] is its main, and the module, if it has one, goes next to it *)
let write_program path text =
  let f = render text in
  Out_channel.with_open_bin path (fun oc -> output_string oc f.main);
  match f.lib with
  | Some lib -> Out_channel.with_open_bin (Filename.concat (Filename.dirname path) (module_name ^ ".stn")) (fun oc -> output_string oc lib)
  | None -> ()

(* what a run printed, with the places of traps left out: the places of a program in two files are not
   those of the same program in one *)
let without_places out =
  String.concat "\n"
    (List.map
       (fun l ->
         if is_prefix "trap: " l then
           match index_of l " at " with Some p -> String.sub l 0 p | None -> l
         else l)
       (String.split_on_char '\n' out))

(* ---------- negative fuzzing (section 21.2) ---------- *)

(* A well-typed program with one mutation that has a known violation must be rejected, with the
   code it names, or with a code of the family. *)
type expect = Code of string | Family of string

let expected_ok expect code =
  match expect with Code c -> code = c | Family f -> is_prefix f code

let show_expect = function Code c -> c | Family f -> f ^ "xx"

(* `let|var NAME: TYPE = ...` : indentation, var or not, name, type *)
let decl_of line =
  let ind = indent_of line in
  let rest = String.sub line ind (String.length line - ind) in
  let strip p = if is_prefix p rest then Some (String.sub rest (String.length p) (String.length rest - String.length p)) else None in
  let parse is_var r =
    match String.index_opt r ':' with
    | Some i when i > 0 && i + 2 < String.length r && r.[i + 1] = ' ' ->
        let name = String.sub r 0 i in
        let tail = String.sub r (i + 2) (String.length r - i - 2) in
        let ident = String.for_all (fun c -> (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_') name in
        let rec find k = if k + 3 > String.length tail then None else if String.sub tail k 3 = " = " then Some k else find (k + 1) in
        (match find 0 with Some k when ident -> Some (ind, is_var, name, String.sub tail 0 k) | _ -> None)
    | _ -> None
  in
  match strip "let " with Some r -> parse false r | None -> (match strip "var " with Some r -> parse true r | None -> None)

let main_index lines =
  let r = ref (-1) in
  Array.iteri (fun i l -> if l = "fn main():" then r := i) lines;
  !r

let ends_with suf s =
  let n = String.length s and m = String.length suf in
  n >= m && String.sub s (n - m) m = suf

(* the generated part of the program starts after the comment that follows the prelude, which is the same
   in every program. Mutations leave the comment where it is. *)
let generated_from lines =
  let k = marker_index lines in
  if k < 0 then Array.length lines else k + 1

(* the last print of main: what comes after it is not part of main *)
let end_of_main lines =
  let r = ref (Array.length lines - 1) in
  Array.iteri (fun i l -> if l = {|    print("end")|} then r := i) lines;
  !r

(* a violation in lines of its own goes before the last print of main, a function of its own before main *)
let before_end lines news = insert_after lines (end_of_main lines - 1) news

let before_main lines news = insert_after lines (main_index lines - 1) news

(* the declarations `let|var NAME: TYPE = ...` of the generated part of the program, at any depth: a
   statement put right after one, with its indentation, is in the scope of the name *)
let decls lines =
  let first = generated_from lines in
  let r = ref [] in
  Array.iteri (fun i l -> if i >= first then match decl_of l with Some (ind, v, n, t) -> r := (i, ind, v, n, t) :: !r | None -> ()) lines;
  List.rev !r

(* the lines of the generated part that are whole statements of a body: a statement put after one,
   with its indentation, goes in the same block. A header, an arm (with its body on the same line or
   not), and the result that ends a function are not among them. *)
let statement_lines lines =
  let first = generated_from lines in
  let last = end_of_main lines in
  let r = ref [] in
  Array.iteri
    (fun i l ->
      let t = String.trim l in
      if i >= first && i <= last && indent_of l >= 4 && t <> "" && t.[0] <> '(' && (not (ends_with ":" t)) && not (contains t "->") then
        r := (i, indent_of l) :: !r)
    lines;
  List.rev !r

let pick rng = function [] -> None | l -> Some (List.nth l (Random.State.int rng (List.length l)))
let pick_decl rng lines ok = pick rng (List.filter (fun (_, _, v, _, t) -> ok v t) (decls lines))

let with_line lines i l =
  let a = Array.copy lines in
  a.(i) <- l;
  a

let at ind s = String.make ind ' ' ^ s

(* what the declaration of a variable can be given instead of its expression *)
let simplest = function
  | "Int" -> Some "0" | "Bool" -> Some "true" | "Str" -> Some "\"\"" | "Array[Int]" -> Some "no_ints()"
  | "Pair" -> Some "Pair(0, \"p\")" | "Shape" -> Some "Dot" | "Int?" -> Some "no_int()" | "any Show" -> Some "7"
  | "Array[any Show]" -> Some "no_shows()" | "any Fig" -> Some "Sq(1)" | "Array[any Fig]" -> Some "no_figs()"
  | "Map[Str, Int]" -> Some "no_counts()" | "Set[Int]" -> Some "no_keys()"
  | "(any Fig)?" -> Some "no_fig()" | "any Chk" -> Some "Lim(3)" | _ -> None

(* an arm of a match over a type with several variants: a line that begins with its pattern *)
let arm_prefixes = [ "Dot ->"; "Box("; "Named("; "Some("; "None ->"; "Ok("; "Err("; "Tri("; "Quad("; "Big(" ]

(* What a violation is written as when it has a variable of its own: statements, which go after one
   of the statements of the program, wherever it is, or items, which go before main. *)
type placement = Statements of string list | Items of string list

let place rng lines = function
  | Items news -> before_main lines news
  | Statements news -> (
      match pick rng (statement_lines lines) with
      | Some (i, ind) -> insert_after lines i (List.map (at ind) news)
      | None -> before_end lines (List.map (at 4) news))

(* What a reduction of a mutation that was accepted keeps, for it to be a violation still: a line of the
   program, or a match with exactly the arms that are left of it. The match is told by its header and by the
   heads of its arms, in order, and the arm that was taken away is not among them: another match in the program
   with the same header and the same arms, and one more, is not it. *)
type witness = Line of string | Match of string * string list

(* One violation of a rule of the language. [in_context] puts it next to a line or a variable of the
   program, and is [None] when the program has none that fits; with the program it gives the lines it
   needs that were there already, which a reduction of the program has to keep for the violation to
   stay. [own] writes it with a variable of its own, anywhere, in one of the ways it has, so that every
   kind is exercised whatever the program has. *)
type mutation = {
  kind : string;
  expect : expect;
  in_context : Random.State.t -> string array -> (string array * witness list) option;
  own : placement list;
}

let ok a = Some (a, [])

let taker t = if t = "Str" then "eat" else "eat_ints"

(* the candidates are lazy: only the one that is picked is built *)
let one_of rng candidates = match pick rng candidates with Some f -> f () | None -> None

let mutations : mutation list =
  [ { kind = "use after take";
      expect = Code "E0302";
      in_context =
        (fun rng lines ->
          match pick_decl rng lines (fun _ t -> t = "Str" || t = "Array[Int]") with
          | Some (i, ind, _, n, t) ->
              ok (insert_after lines i [ at ind (sprintf "let moved_%s = %s(take %s)" n (taker t) n); at ind (sprintf "print(f\"{len(%s)}\")" n) ])
          | None -> None);
      own = [ Statements [ "let neg_s: Str = \"x\""; "let neg_t = eat(take neg_s)"; "print(f\"{len(neg_s)}\")" ] ] };
    { kind = "take in a loop";
      expect = Code "E0302";
      in_context =
        (fun rng lines ->
          (* a variable of its own before a loop of the program, taken as the loop's first statement *)
          let first = generated_from lines in
          let found = ref [] in
          Array.iteri
            (fun j l ->
              let t = String.trim l in
              if j >= first && (is_prefix "for " t || is_prefix "while " t) && j + 1 < Array.length lines && indent_of lines.(j + 1) > indent_of l
              then found := j :: !found)
            lines;
          match pick rng !found with
          | Some j ->
              let take = at (indent_of lines.(j + 1)) "let neg_t = eat(take neg_s)" in
              Some (insert_after (insert_after lines j [ take ]) (j - 1) [ at (indent_of lines.(j)) "let neg_s: Str = \"x\"" ], [ Line (String.trim lines.(j)) ])
          | None -> None);
      own = [ Statements [ "let neg_s: Str = \"x\""; "for neg_i in [1, 2]:"; "    let neg_t = eat(take neg_s)" ] ] };
    { kind = "mut marker left out";
      expect = Code "E0304";
      in_context =
        (fun rng lines ->
          (* a call of the program that passes a mutable place as mut, with the marker taken off; or a
             call of sort with the marker left off a variable of the program *)
          let calls = ref [] in
          Array.iteri
            (fun i l ->
              if (not (is_prefix "fn " (String.trim l))) && indent_of l >= 4
                 && (contains l "grow(mut " || contains l "replace_fig(mut " || contains l "sort(mut ")
              then calls := (fun () -> match replace_first lines.(i) "(mut " "(" with Some l -> ok (with_line lines i l) | None -> None) :: !calls)
            lines;
          let vars =
            List.map
              (fun (i, ind, _, n, _) () -> ok (insert_after lines i [ at ind (sprintf "sort(%s)" n) ]))
              (List.filter (fun (_, _, v, _, t) -> v && t = "Array[Int]") (decls lines))
          in
          one_of rng (!calls @ vars));
      own = [ Statements [ "var neg_xs: Array[Int] = [3, 1, 2]"; "sort(neg_xs)" ] ] };
    { kind = "mut of an immutable";
      expect = Code "E0303";
      in_context =
        (fun rng lines ->
          match pick_decl rng lines (fun v t -> (not v) && (t = "Array[Int]" || t = "Array[any Fig]")) with
          | Some (i, ind, _, n, t) ->
              let use =
                if t = "Array[Int]" then (if Random.State.bool rng then sprintf "sort(mut %s)" n else sprintf "%s.push(1)" n)
                else sprintf "grow(mut %s, Sq(1))" n
              in
              ok (insert_after lines i [ at ind use ])
          | None -> None);
      own = [ Statements [ "let neg_xs: Array[Int] = [3, 1, 2]"; "sort(mut neg_xs)" ] ] };
    { kind = "assignment to an immutable";
      expect = Code "E0103";
      in_context =
        (fun rng lines ->
          match pick_decl rng lines (fun v t -> (not v) && simplest t <> None) with
          | Some (i, ind, _, n, t) -> ok (insert_after lines i [ at ind (sprintf "%s = %s" n (Option.get (simplest t))) ])
          | None -> None);
      own = [ Statements [ "let neg_n: Int = 1"; "neg_n = 2" ] ] };
    { kind = "overlapping mut arguments";
      expect = Code "E0301";
      in_context =
        (fun rng lines ->
          match pick_decl rng lines (fun v t -> v && t = "Array[Int]") with
          | Some (i, ind, _, n, _) -> ok (insert_after lines i [ at ind (sprintf "two_mut(mut %s, mut %s)" n n) ])
          | None -> None);
      own = [ Statements [ "var neg_xs: Array[Int] = [1]"; "two_mut(mut neg_xs, mut neg_xs)" ] ] };
    { kind = "closure over a mut argument";
      expect = Code "E0305";
      in_context =
        (fun rng lines ->
          match pick_decl rng lines (fun v t -> v && t = "Array[Int]") with
          | Some (i, ind, _, n, _) -> ok (insert_after lines i [ at ind (sprintf "with_cb(mut %s, fn(): len(%s))" n n) ])
          | None -> None);
      own = [ Statements [ "var neg_xs: Array[Int] = [1]"; "with_cb(mut neg_xs, fn(): len(neg_xs))" ] ] };
    { kind = "arm of a match left out";
      expect = Code "E0202";
      in_context =
        (fun rng lines ->
          let found = ref [] in
          Array.iteri
            (fun i l ->
              let t = String.trim l in
              if indent_of l > 0 && List.exists (fun p -> is_prefix p t) arm_prefixes && contains t "->" then found := i :: !found)
            lines;
          match pick rng !found with
          | Some i ->
              (* the line above it that is less indented is the header of the match *)
              let h = ref (i - 1) in
              while !h > 0 && (blank lines.(!h) || indent_of lines.(!h) >= indent_of lines.(i)) do decr h done;
              (* a reduction keeps the match and the arms that are left, so that it is still one that does not
                 cover every case: it can only take arms away, and one that is missing stays missing *)
              let arms = ref [] in
              let k = ref (!h + 1) in
              while !k < Array.length lines && (blank lines.(!k) || indent_of lines.(!k) > indent_of lines.(!h)) do
                if !k <> i && (not (blank lines.(!k))) && indent_of lines.(!k) = indent_of lines.(i) then arms := String.trim lines.(!k) :: !arms;
                incr k
              done;
              Some (delete_lines lines i (group_at lines i), [ Match (String.trim lines.(!h), List.rev !arms) ])
          | None -> None);
      own = [ Statements [ "match Some(1):"; "    Some(neg_n) ->"; "        print(\"a\")" ] ] };
    { kind = "unknown name";
      expect = Code "E0101";
      in_context =
        (fun rng lines ->
          (* a variable of the program with a letter more *)
          match pick_decl rng lines (fun _ _ -> true) with
          | Some (i, ind, _, n, _) -> ok (insert_after lines i [ at ind (sprintf "print(f\"{%sx}\")" n) ])
          | None -> None);
      own = [ Statements [ "print(neg_unknown)" ] ] };
    { kind = "too few arguments";
      expect = Code "E0203";
      in_context = (fun _ _ -> None);
      own = [ Statements [ "print(f\"{via_any(Sq(1))}\")" ] ] };
    { kind = "argument of another type";
      expect = Code "E0201";
      in_context = (fun _ _ -> None);
      own = [ Statements [ "print(f\"{via_any(Sq(1), true)}\")" ] ] };
    { kind = "annotation of another type";
      expect = Family "E02";
      in_context =
        (fun rng lines ->
          match pick_decl rng lines (fun _ t -> t = "Int" || t = "Bool" || t = "Str") with
          | Some (i, _, _, _, t) -> (
              let other = List.filter (fun u -> u <> t) [ "Int"; "Bool"; "Str" ] in
              let u = List.nth other (Random.State.int rng (List.length other)) in
              match replace_first lines.(i) (sprintf ": %s = " t) (sprintf ": %s = " u) with
              | Some l -> ok (with_line lines i l)
              | None -> None)
          | None -> None);
      own = [ Statements [ "let neg_n: Str = 1" ] ] };
    { kind = "result of another type";
      expect = Family "E02";
      in_context =
        (fun rng lines ->
          let found = ref [] in
          Array.iteri (fun i l -> if is_prefix "fn f" l && contains l ") -> Int:" then found := i :: !found) lines;
          match pick rng !found with
          | Some i -> (match replace_first lines.(i) ") -> Int:" ") -> Str:" with Some l -> ok (with_line lines i l) | None -> None)
          | None -> None);
      own = [ Items [ "fn neg_f() -> Str:"; "    1"; "" ] ] };
    { kind = "error not listed by an exported function";
      expect = Code "E0501";
      in_context = (fun _ _ -> None);
      own = [ Items [ "fn neg_g*(n: Int) -> Int:"; "    must_check(Lim(3), n)"; "" ] ] };
    { kind = "element type never settled";
      expect = Code "E0210";
      in_context = (fun _ _ -> None);
      own = [ Statements [ "let neg_empty = []" ]; Statements [ "let neg_none = None" ] ] };
    { kind = "type arguments after a function that is not generic";
      expect = Code "E0102";
      in_context = (fun _ _ -> None);
      own = [ Items [ "fn neg_plain(x: Int) -> Int:"; "    x"; ""; "fn neg_plain_call() -> Int:"; "    neg_plain[Int](1)"; "" ] ] };
    { kind = "too many type arguments";
      expect = Code "E0203";
      in_context = (fun _ _ -> None);
      own = [ Items [ "fn neg_one[T](x: T) -> T:"; "    x"; ""; "fn neg_one_call() -> Int:"; "    neg_one[Int, Str](1)"; "" ] ] };
    { kind = "explicit type argument that breaks a bound";
      expect = Code "E0204";
      in_context = (fun _ _ -> None);
      own = [ Items [ "type NegPlain = struct(k: Int)"; ""; "fn neg_label[T: Show](x: T) -> Str:"; "    f\"[{x}]\""; "";
                      "fn neg_label_call() -> Str:"; "    neg_label[NegPlain](NegPlain(1))"; "" ] ] };
    { kind = "impl that adds a bound to a method";
      expect = Code "E0204";
      in_context = (fun _ _ -> None);
      own = [ Items [ "trait NegExtra:"; "    fn neg_extra(x: Self) -> Int"; ""; "trait NegMapper:"; "    fn neg_map[U](x: Self, v: U) -> Int"; "";
                      "type NegBox = struct(n: Int)"; ""; "impl NegMapper for NegBox:"; "    fn neg_map[U: NegExtra](x: NegBox, v: U) -> Int:";
                      "        v.neg_extra() + x.n"; "" ] ] };
    { kind = "field named twice";
      expect = Code "E0101";
      in_context =
        (fun rng lines ->
          (* a struct of the program, with its first field once more *)
          let found = ref [] in
          Array.iteri (fun i l -> if is_prefix "type " l && contains l " = struct(" && ends_with ")" l then found := i :: !found) lines;
          match pick rng !found with
          | Some i -> (
              let l = lines.(i) in
              match index_of l "struct(" with
              | Some p -> (
                  match String.index_from_opt l (p + 7) ':' with
                  | Some q -> ok (with_line lines i (String.sub l 0 (String.length l - 1) ^ ", " ^ String.sub l (p + 7) (q - p - 7) ^ ": Int)"))
                  | None -> None)
              | None -> None)
          | None -> None);
      own = [ Items [ "type NegDup = struct(a: Int, b: Int, a: Str)"; "" ]; Items [ "type NegDup = A | B(a: Int, a: Int)"; "" ] ] };
    { kind = "type parameter named twice";
      expect = Code "E0101";
      in_context = (fun _ _ -> None);
      own =
        [ Items [ "fn neg_pick[T, T](a: T, b: T) -> T:"; "    a"; "" ];
          Items [ "type NegPair[A, A] = struct(first: A, second: A)"; "" ];
          Items [ "trait NegConvert[A, A]:"; "    fn convert(x: Self) -> Int"; "" ];
          Items [ "type NegBox[T] = struct(item: T)"; "impl[T, T] Show for NegBox[T]:"; "    fn show(b: NegBox[T]) -> Str:"; "        \"box\""; "" ] ] };
    { kind = "argument given twice";
      expect = Code "E0203";
      in_context = (fun _ _ -> None);
      own =
        [ Statements [ "print(f\"{via_any(Sq(1), k=1, k=2)}\")" ];
          Statements [ "print(f\"{via_any(Sq(1), 1, k=2)}\")" ];
          Statements [ "print(f\"{Sq(side=1, side=2).side}\")" ] ] } ]

(* the code of the first diagnostic that `check --json` wrote *)
let json_code out =
  let key = "\"code\":\"" in
  let n = String.length out and m = String.length key in
  let rec find i = if i + m > n then None else if String.sub out i m = key then Some (i + m) else find (i + 1) in
  match find 0 with
  | Some i -> (match String.index_from_opt out i '"' with Some j -> Some (String.sub out i (j - i)) | None -> None)
  | None -> None

(* ---------- shrinking (section 21.2) ---------- *)

(* how long one run of the compiler may take, in seconds. A shrink shortens it: its candidates have
   things taken out, and one that loops costs a whole limit. *)
let time_limit = ref 120.0

(* where the programs of a shrink are written: the scratch directory, or for --reduce the directory of the
   input, which is where a compiler looks for what the input imports. In that directory a file is made, with
   a name that nothing had, when it is first wanted; its path is kept, and the files made are the only ones
   that are removed at the end. *)
let candidate_dir : string option ref = ref None
let candidate_files : (string, string) Hashtbl.t = Hashtbl.create 4
let candidates_made : string list ref = ref []

(* the part of the name of a scratch file that is not what it is for: a process number and random bits, or
   in a test the tokens that FUZZ_SCRATCH_TOKENS has, separated by commas, in the order they are wanted, so that
   a name that is taken can be made the first to be tried *)
let scratch_tokens = ref (match Sys.getenv_opt "FUZZ_SCRATCH_TOKENS" with Some s -> String.split_on_char ',' s | None -> [])

let next_scratch_token () =
  match !scratch_tokens with
  | t :: rest -> scratch_tokens := rest; t
  | [] -> sprintf "%d-%08x" (Unix.getpid ()) (Random.bits ())

let candidate_path tmp name =
  match !candidate_dir with
  | None -> Filename.concat tmp (name ^ ".stn")
  | Some dir -> (
      match Hashtbl.find_opt candidate_files name with
      | Some p -> p
      | None ->
          let rec make k =
            let p = Filename.concat dir (sprintf ".fuzz-reduce-%s-%s.stn" (next_scratch_token ()) name) in
            match Unix.openfile p [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL ] 0o600 with
            | fd -> Unix.close fd; p
            | exception Unix.Unix_error (Unix.EEXIST, _, _) when k < 100 -> make (k + 1)
          in
          let p = make 0 in
          Hashtbl.replace candidate_files name p;
          candidates_made := p :: !candidates_made;
          p)

(* simpler versions of a line: a declaration with the simplest expression of its type, a print of
   nothing, and its integers made 0 *)
let simpler line =
  let ind = indent_of line in
  let pad = String.make ind ' ' in
  let decl =
    match decl_of line with
    | Some (_, v, n, t) -> (
        match simplest t with
        | Some e ->
            let l = sprintf "%s%s %s: %s = %s" pad (if v then "var" else "let") n t e in
            if l <> line then [ l ] else []
        | None -> [])
    | None -> []
  in
  let print =
    let t = String.trim line in
    if is_prefix "print(" t && t <> "print(\"\")" then [ pad ^ "print(\"\")" ] else []
  in
  let ints =
    let b = Buffer.create (String.length line) in
    let n = String.length line in
    let i = ref 0 in
    while !i < n do
      let c = line.[!i] in
      let prev_ident = !i > 0 && (let p = line.[!i - 1] in (p >= 'a' && p <= 'z') || (p >= 'A' && p <= 'Z') || p = '_' || (p >= '0' && p <= '9')) in
      if c >= '0' && c <= '9' && not prev_ident then begin
        let j = ref !i in
        while !j < n && line.[!j] >= '0' && line.[!j] <= '9' do incr j done;
        let num = String.sub line !i (!j - !i) in
        Buffer.add_string b (if num = "0" || num = "1" then num else "0");
        i := !j
      end
      else (Buffer.add_char b c; incr i)
    done;
    let l = Buffer.contents b in
    if l <> line then [ l ] else []
  in
  decl @ print @ ints

let dedent by l = if indent_of l >= by then String.sub l by (String.length l - by) else l

(* What a statement that has a body can be replaced by, out of what is in it: a loop or an if by its
   body (an if with an else: by the body of either part), a match by the body of one of its arms, which
   is the statements under the arm or the expression after its arrow. The bindings of the arm are
   gone then, which the check tells. *)
let unwraps lines i =
  let n = Array.length lines in
  let ind = indent_of lines.(i) in
  let t = String.trim lines.(i) in
  let j = group_at lines i in
  let sub a b = Array.sub lines a (b - a) in
  let replace news = Array.concat [ Array.sub lines 0 i; news; Array.sub lines j (n - j) ] in
  let deeper_end k =
    let e = ref k in
    while !e < n && (not (blank lines.(!e))) && indent_of lines.(!e) > ind do incr e done;
    !e
  in
  if not (ends_with ":" t) then []
  else if is_prefix "for " t || is_prefix "while " t then [ replace (Array.map (dedent 4) (sub (i + 1) j)) ]
  else if is_prefix "if " t then begin
    let e = deeper_end (i + 1) in
    let then_ = replace (Array.map (dedent 4) (sub (i + 1) e)) in
    if e < n && indent_of lines.(e) = ind && String.trim lines.(e) = "else:" then [ then_; replace (Array.map (dedent 4) (sub (e + 1) j)) ]
    else [ then_ ]
  end
  else if is_prefix "match " t then begin
    let arms = ref [] in
    for k = i + 1 to j - 1 do
      if (not (blank lines.(k))) && indent_of lines.(k) = ind + 4 then begin
        let a = String.trim lines.(k) in
        if ends_with "->" a then begin
          let e = ref (k + 1) in
          while !e < j && (not (blank lines.(!e))) && indent_of lines.(!e) > ind + 4 do incr e done;
          if !e > k + 1 then arms := replace (Array.map (dedent 8) (sub (k + 1) !e)) :: !arms
        end
        else
          match replace_first a " -> " "\000" with
          | Some r -> (
              match String.index_opt r '\000' with
              | Some p -> arms := replace [| at ind (String.sub r (p + 1) (String.length r - p - 1)) |] :: !arms
              | None -> ())
          | None -> ()
      end
    done;
    List.rev !arms
  end
  else []

(* blank lines left where items were taken out: at most one in a row, none at the start *)
let squeeze lines =
  let out = ref [] and prev_blank = ref true in
  Array.iter
    (fun l ->
      if blank l then begin
        if not !prev_blank then out := "" :: !out;
        prev_blank := true
      end
      else (out := l :: !out; prev_blank := false))
    lines;
  Array.of_list (List.rev !out)

(* Take away statements and items while [still_fails] holds, then simplify what is left. Each pass
   goes down the program, trying to delete the line it is at with what is under it, which takes the
   large pieces first, or to put the body of a statement in its place; the passes repeat until nothing
   more goes. *)
let shrink ?(budget = 400) ~still_fails text =
  let saved_limit = !time_limit in
  time_limit := Float.min saved_limit 15.0;
  let evals = ref 0 in
  let attempt lines =
    incr evals;
    still_fails (text_of lines)
  in
  let cur = ref (lines_of text) in
  let progress = ref true in
  while !progress && !evals < budget do
    progress := false;
    let i = ref 0 in
    while !i < Array.length !cur && !evals < budget do
      (* the comments say how the program is written to files, and stay *)
      if blank !cur.(!i) || is_prefix "#" (String.trim !cur.(!i)) then incr i
      else begin
        let cand = delete_lines !cur !i (group_at !cur !i) in
        if attempt cand then (cur := cand; progress := true)
        else
          match List.find_opt (fun c -> !evals < budget && attempt c) (unwraps !cur !i) with
          | Some c -> cur := c; progress := true
          | None -> incr i
      end
    done;
    let i = ref 0 in
    while !i < Array.length !cur && !evals < budget do
      let l = !cur.(!i) in
      (match List.find_opt (fun v -> !evals < budget && (let c = Array.copy !cur in c.(!i) <- v; attempt c)) (simpler l) with
       | Some v -> !cur.(!i) <- v; progress := true
       | None -> ());
      incr i
    done
  done;
  (* the blank lines go last, and only if the program still fails without them *)
  let squeezed = squeeze !cur in
  if squeezed <> !cur && attempt squeezed then cur := squeezed;
  time_limit := saved_limit;
  (text_of !cur, !evals)

(* ---------- running the compiler ---------- *)

exception Hang of string

let read_file path = In_channel.with_open_bin path In_channel.input_all

(* How a process ended: with a status, or killed by a signal (an OCaml signal number) *)
type outcome = Exited of int | Signaled of int

(* Run a command, with its output in temporary files and a time limit. With [separate] the standard error is
   in a file of its own, so that what a compiler says of itself is not taken for what a program prints; without
   it both go to one file, in the order they were written, and the last of the three is empty. [what] says what
   was run, for the report of one that does not end. *)
let spawn ~separate tmp (argv : string array) what : outcome * string * string =
  let out = Filename.concat tmp "out.txt" and err = Filename.concat tmp "err.txt" in
  let open_file p = Unix.openfile p [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
  let fd = open_file out in
  let efd = if separate then open_file err else fd in
  (* the compiler runs the program it builds as a child of its own, so each invocation
     gets a process group of its own, and the whole group is killed afterwards *)
  let pid =
    match Unix.fork () with
    | 0 -> (
        try
          ignore (Unix.setsid ());
          Unix.dup2 fd Unix.stdout;
          Unix.dup2 efd Unix.stderr;
          (* execvp searches PATH, so STARNITE may name an installed command *)
          Unix.execvp argv.(0) argv
        with e ->
          prerr_string (sprintf "fuzz: cannot run %s: %s\n" argv.(0) (Printexc.to_string e));
          flush stderr;
          Unix._exit 127)
    | pid -> pid
  in
  Unix.close fd;
  if separate then Unix.close efd;
  let kill_group () = try Unix.kill (-pid) Sys.sigkill with Unix.Unix_error _ -> () in
  let deadline = Unix.gettimeofday () +. !time_limit in
  let rec wait () =
    match Unix.waitpid [ Unix.WNOHANG ] pid with
    | 0, _ ->
        if Unix.gettimeofday () > deadline then begin
          kill_group ();
          ignore (Unix.waitpid [] pid);
          raise (Hang what)
        end;
        Unix.sleepf 0.01;
        wait ()
    | _, Unix.WEXITED c -> Exited c
    | _, (Unix.WSIGNALED s | Unix.WSTOPPED s) -> Signaled s
  in
  let outcome = wait () in
  (* nothing the invocation started may outlive it and write to the next case's output *)
  kill_group ();
  (outcome, read_file out, if separate then read_file err else "")

(* Run the compiler on a file, with its output in a temporary file and a time limit. *)
let run starnite tmp args path : int * string =
  match spawn ~separate:false tmp (Array.of_list ((starnite :: args) @ [ path ])) (String.concat " " args) with
  | Exited c, out, _ -> (c, out)
  | Signaled s, out, _ -> (128 + abs s, out)

(* the same, with what the program printed and what it said on the standard error kept apart *)
let run_apart starnite tmp args path : int * string * string =
  match spawn ~separate:true tmp (Array.of_list ((starnite :: args) @ [ path ])) (String.concat " " args) with
  | Exited c, out, err -> (c, out, err)
  | Signaled s, out, err -> (128 + abs s, out, err)

let tail s n = if String.length s <= n then s else String.sub s (String.length s - n) n

let first_difference a b =
  let rec go = function
    | x :: xs, y :: ys -> if x <> y then Some (x, y) else go (xs, ys)
    | _ -> None
  in
  go (String.split_on_char '\n' a, String.split_on_char '\n' b)

(* The oracles of a program: it checks, and the interpreter and the C build agree. A program that is split
   across a module is also the one file that its text is, and the interpreter must do the same with that.
   A shrink for the difference between the two does not need the C build. *)
let differential ?(c_build = true) starnite tmp path text =
  write_program path text;
  let ci, oi = run starnite tmp [ "check" ] path in
  if ci = 127 then begin
    (* the compiler did not start at all: no case can be judged *)
    prerr_string oi;
    exit 2
  end;
  if ci <> 0 then `Rejected oi
  else
    let ri, out_i = run starnite tmp [ "run"; "--interp" ] path in
    let rc, out_c = if c_build then run starnite tmp [ "run" ] path else (ri, out_i) in
    if ri <> rc || out_i <> out_c then `Differ (ri, out_i, rc, out_c)
    else if not (is_split text) then `Agreed
    else begin
      let twin = Filename.concat tmp "twin.stn" in
      Out_channel.with_open_bin twin (fun oc -> output_string oc text);
      (* what a program prints is the same byte for byte; only the places in the traps it reports, on the standard
         error, are not (they are those of two files and of one) *)
      let rs, so, se = run_apart starnite tmp [ "run"; "--interp" ] path in
      let rt, to_, te = run_apart starnite tmp [ "run"; "--interp" ] twin in
      if rt = rs && so = to_ && without_places se = without_places te then `Agreed
      else `Twin (rs, so ^ se, rt, to_ ^ te)
    end

(* what makes a program fail the same way: it checks, and it still fails in the way it did, with the
   statuses it ended with *)
let still_differs starnite tmp kind text =
  let p = candidate_path tmp "shrink" in
  let c_build = match kind with `Differ _ -> true | `Twin _ -> false in
  match differential ~c_build starnite tmp p text with
  | `Differ (ri, _, rc, _) -> (match kind with `Differ (ri0, rc0) -> ri = ri0 && rc = rc0 | `Twin _ -> false)
  | `Twin (ri, _, rt, _) -> (match kind with `Twin (ri0, rt0) -> ri = ri0 && rt = rt0 | `Differ _ -> false)
  | `Agreed | `Rejected _ -> false
  | exception Hang _ -> false

(* the matches of a text: the header of each, and the heads of its arms, in order *)
let matches_of lines =
  let n = Array.length lines in
  let r = ref [] in
  Array.iteri
    (fun h l ->
      let t = String.trim l in
      if is_prefix "match " t && ends_with ":" t then begin
        let ind = indent_of l in
        let k = ref (h + 1) and arm_ind = ref (-1) and arms = ref [] in
        while !k < n && (blank lines.(!k) || indent_of lines.(!k) > ind) do
          if not (blank lines.(!k)) then begin
            if !arm_ind < 0 then arm_ind := indent_of lines.(!k);
            if indent_of lines.(!k) = !arm_ind then arms := String.trim lines.(!k) :: !arms
          end;
          incr k
        done;
        r := (t, List.rev !arms) :: !r
      end)
    lines;
  !r

let holds text witnesses =
  let ms = lazy (matches_of (lines_of text)) in
  List.for_all (function Line s -> contains text s | Match (h, arms) -> List.mem (h, arms) (Lazy.force ms)) witnesses

(* what makes a mutated program that was accepted fail the same way: it is accepted, and still has what makes
   the violation *)
let still_has starnite tmp witnesses text =
  let p = candidate_path tmp "shrink" in
  write_program p text;
  holds text witnesses
  && (match run starnite tmp [ "check" ] p with 0, _ -> true | _ -> false | exception Hang _ -> false)

(* The mutation of the program of a seed: its kind, the program with the violation in it, whether the
   violation is made of a line or a variable of the program, and the lines of the program that it
   needs. Every kind is as likely as any other. When the program has a line or a variable to use, half
   of the time the violation is made of it; otherwise it is written with a variable of its own, after
   a statement that is anywhere in the program. *)
let mutate case prog =
  let rng = Random.State.make [| case; 0x6e65 |] in
  let lines = lines_of prog in
  let m = List.nth mutations (Random.State.int rng (List.length mutations)) in
  match m.in_context rng lines with
  | Some (a, essential) when Random.State.bool rng -> (m, text_of a, true, essential)
  | _ -> (m, text_of (place rng lines (List.nth m.own (Random.State.int rng (List.length m.own)))), false, [])

(* the lines of [b] that [a] does not have *)
let added_lines a b =
  let seen = Hashtbl.create 256 in
  Array.iter (fun l -> Hashtbl.replace seen l ()) a;
  List.filter (fun l -> not (Hashtbl.mem seen l)) (Array.to_list b)

(* what makes a mutated program fail the same way: the checker rejects it with the code it was rejected with *)
let still_rejected starnite tmp code text =
  let p = candidate_path tmp "shrink" in
  write_program p text;
  match run starnite tmp [ "check"; "--json" ] p with
  | 0, _ -> false
  | _, out -> json_code out = Some code
  | exception Hang _ -> false

(* ---------- the compiler must not crash (section 21.2, the first oracle) ---------- *)

(* A change to the bytes of a text, with no regard for what it says: a character taken out, the text cut
   short, a character replaced by a punctuation mark or a letter, a piece of it repeated or taken out, two
   characters swapped. The program is then in most cases wrong in some way that no rule of the language
   was written for, and whatever the compiler says of it, it must say. *)
let corrupt rng text =
  let b = Bytes.of_string text in
  let n = Bytes.length b in
  if n = 0 then text
  else
    let cut p m = Bytes.cat (Bytes.sub b 0 p) (Bytes.sub b (p + m) (n - p - m)) in
    match Random.State.int rng 6 with
    | 0 -> Bytes.to_string (cut (Random.State.int rng n) 1)
    | 1 -> Bytes.to_string (Bytes.sub b 0 (Random.State.int rng n))
    | 2 ->
        let marks = "()[]{}:,.=+-*/%<>!?&|\"'#\\\n _0aZ" in
        Bytes.set b (Random.State.int rng n) marks.[Random.State.int rng (String.length marks)];
        Bytes.to_string b
    | 3 ->
        let p = Random.State.int rng n in
        let m = min (n - p) (1 + Random.State.int rng 20) in
        Bytes.to_string (Bytes.cat (Bytes.sub b 0 (p + m)) (Bytes.sub b p (n - p)))
    | 4 ->
        let p = Random.State.int rng n in
        Bytes.to_string (cut p (min (n - p) (1 + Random.State.int rng 30)))
    | _ ->
        let p = Random.State.int rng n and q = Random.State.int rng n in
        let c = Bytes.get b p in
        Bytes.set b p (Bytes.get b q);
        Bytes.set b q c;
        Bytes.to_string b

(* where a compiler crashed: in the check, or in what builds and runs a program that checks. The second is
   named by what ran: "run --interp", "build" (the compiler and the C compiler), or "exe" (the program it built), and for
   the last two by how it ended, a status or a signal: a shrink keeps the failure it was given, not another one *)
(* the ones that end in a hang are kept apart: a candidate that ends in a regular answer after a longer time is not the same failure *)
type crash = At_check | At_check_hung | At_run of string list | At_run_hung of string list

(* A line that OCaml writes when an exception nothing caught ends a process. It is the compiler's own: the
   programs it builds print on the standard output, and say what went wrong on the standard error in lines
   of a few forms that do not begin like this. *)
let uncaught err = List.exists (is_prefix "Fatal error: exception") (String.split_on_char '\n' err)

(* The compiler's own report that a program uses what a backend does not support yet (`Unsupported`, which exits
   1 before the C compiler runs): a line that is that report, and nothing of a fatal exception or of a C compiler
   that failed. The words anywhere else in the output are not it. *)
let unsupported err =
  let ls = String.split_on_char '\n' err in
  List.exists (is_prefix "error: not supported yet: ") ls
  && (not (uncaught err))
  && not (List.exists (is_prefix "error: the C compiler failed") ls)

(* A process killed by a signal. A trap is an exit with a status, and so is the C build's stack overflow, so a
   signal is a fault of the compiler or of the runtime, or of the machine (a kill for want of memory); a run
   that the fuzzer ended for taking too long is not here, it is the exception Hang. *)
let died_by_signal = function Signaled _ -> true | Exited _ -> false

(* what the compiler does with a program that may be wrong: a crash, or nothing to say. What it prints and
   what a program prints are kept apart (the standard output and the standard error of each step), the C build
   is a step of its own, and the program it makes is run by the fuzzer: a program that prints a line that looks
   like a crash is not one, a program or a build killed by a signal is, and a build that does not end is. *)
let crash_of starnite tmp path text =
  write_program path text;
  let exe = Filename.concat tmp "crash.exe" in
  let step args = spawn ~separate:true tmp (Array.of_list ((starnite :: args) @ [ path ])) (String.concat " " args) in
  match step [ "check"; "--json" ] with
  | exception Hang _ -> Some (At_check_hung, "the check did not end")
  | Signaled s, _, err -> Some (At_check, sprintf "killed by signal %d\n%s" (abs s) err)
  | Exited c, out, err when c >= 2 || uncaught err -> Some (At_check, err ^ out)
  | Exited 0, _, _ -> (
      (* it checks: it must run, on both backends, though it may run for ever or trap *)
      let interp =
        match step [ "run"; "--interp" ] with
        | exception Hang _ -> None
        | o, out, err ->
            if died_by_signal o || uncaught err then Some (At_run [ "run"; "--interp" ], err ^ out) else None
      in
      match interp with
      | Some c -> Some c
      | None -> (
          (try Sys.remove exe with Sys_error _ -> ());
          match step [ "build"; "-o"; exe ] with
          | exception Hang _ -> Some (At_run_hung [ "build" ], "the build did not end")
          | Signaled s, _, err -> Some (At_run [ "build"; sprintf "signal %d" (abs s) ], sprintf "killed by signal %d\n%s" (abs s) err)
          | Exited c, out, err when c <> 0 && not (c = 1 && unsupported err) ->
              (* a program that checked is built, or the compiler says it cannot yet (valid code that a backend
                 does not support, which is not a crash); the C compiler failing, with or without a word, is *)
              Some (At_run [ "build"; sprintf "status %d" c ], err ^ out)
          | Exited 0, _, _ -> (
              match spawn ~separate:true tmp [| exe |] "the program" with
              | exception Hang _ -> None
              | o, out, err ->
                  let said = if err = "" then out else err in
                  (match o with
                   | Signaled s -> Some (At_run [ "exe"; sprintf "signal %d" (abs s) ], sprintf "the program was killed by a signal\n%s" said)
                   | Exited c when c > 2 ->
                       (* 0 and 1 are what main ends with, 2 is a trap; 3 is the debug runtime finding objects that
                          do not balance, 127 is a program that did not start: neither is the program's own *)
                       Some (At_run [ "exe"; sprintf "status %d" c ], sprintf "the program ended with status %d\n%s" c said)
                   | Exited _ -> None))
          | _ -> None))
  | _ -> None

let still_crashes starnite tmp kind text =
  let p = candidate_path tmp "shrink" in
  match crash_of starnite tmp p text with Some (k, _) -> k = kind | None -> false

let () =
  let count = ref 50 and seed = ref None and keep = ref None and print_only = ref false in
  let shrink_failures = ref false and reduce = ref None and keeping = ref [] and keeping_match = ref None and match_arms = ref [] and rejected = ref None and budget = ref 400 in
  let negative = ref true and differential_runs = ref true and print_mutated = ref false and write_dir = ref None and crash_mode = ref false and corruptions = ref 4 in
  Arg.parse
    [ ("--count", Arg.Set_int count, "N  number of programs (default 50)");
      ("--print", Arg.Set print_only, "  print the program of the seed given by --seed and stop");
      ("--write", Arg.String (fun d -> write_dir := Some d), "DIR  with --print: write the program as the files the compiler is given, main.stn and, if it is split, fuzzlib.stn, instead of printing it");
      ("--mutated", Arg.Set print_mutated, "  with --print: print its mutation instead, the kind and the code it must be rejected with on stderr");
      ("--seed", Arg.Int (fun s -> seed := Some s), "S  first seed (default random)");
      ("--keep", Arg.String (fun d -> keep := Some d), "DIR  save failing programs in DIR");
      ("--shrink", Arg.Set shrink_failures, "  shrink each failing program (at most three), saving caseN.min.stn in the --keep directory");
      ("--shrink-budget", Arg.Set_int budget, "N  how many checks a shrink may make (default 400)");
      ("--reduce", Arg.String (fun f -> reduce := Some f), "FILE  shrink the failing program in FILE, print the result, and stop");
      ("--keeping", Arg.String (fun t -> keeping := !keeping @ [ t ]), "TEXT  with --reduce: keep what compiles and contains TEXT (more than once: all of them), instead of what fails (for a mutation that was accepted)");
      ("--keeping-match", Arg.String (fun h -> keeping_match := Some h), "HEADER  with --reduce: keep a match with this header and exactly the arms given by --arm, in order (for an arm of a match that was taken away)");
      ("--arm", Arg.String (fun a -> match_arms := !match_arms @ [ a ]), "HEAD  with --keeping-match: the head of an arm of that match");
      ("--rejected", Arg.String (fun c -> rejected := Some c), "CODE  with --reduce: keep what the checker rejects with CODE (for a mutation rejected with the wrong code)");
      ("--no-negative", Arg.Clear negative, "  do not mutate programs to be rejected");
      ("--crash", Arg.Set crash_mode, "  instead of the other oracles, corrupt the bytes of each program and require the compiler not to crash");
      ("--corruptions", Arg.Set_int corruptions, "N  with --crash: how many corruptions of each program (default 4)");
      ("--negative-only", Arg.Clear differential_runs, "  only the mutated programs: no run of the interpreter or the C build") ]
    (fun a -> raise (Arg.Bad ("unexpected argument " ^ a)))
    "usage: fuzz.exe [--count N] [--seed S] [--keep DIR] [--shrink] [--reduce FILE [--keeping TEXT | --rejected CODE]]";
  let root = Filename.dirname (Filename.dirname (Filename.dirname (Sys.executable_name))) in
  let starnite =
    match Sys.getenv_opt "STARNITE" with
    | Some s -> s
    | None ->
        (* _build/default/tests/fuzz/fuzz.exe -> _build/default/compiler/main.exe *)
        Filename.concat (Filename.concat root "compiler") "main.exe"
  in
  Random.self_init ();
  (* Random.bits gives 30 random bits; Random.int needs a bound below 2^30 *)
  let seed = match !seed with Some s -> s | None -> Random.bits () in
  if !print_only then begin
    let prog = program seed in
    let text =
      if !print_mutated then begin
        let m, text, in_context, _ = mutate seed prog in
        Printf.eprintf "%s, to be rejected with %s%s\n" m.kind (show_expect m.expect) (if in_context then ", made of the program's own lines" else "");
        text
      end
      else prog
    in
    (match !write_dir with
     | Some dir ->
         (try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
         write_program (Filename.concat dir "main.stn") text
     | None -> print_string text);
    exit 0
  end;
  let tmp = Filename.concat (Filename.get_temp_dir_name ()) (sprintf "starnite-fuzz-%d-%08x" (Unix.getpid ()) (Random.bits ())) in
  Unix.mkdir tmp 0o700;
  let cleanup () =
    List.iter (fun f -> try Sys.remove (Filename.concat tmp f) with Sys_error _ -> ()) [ "out.txt"; "err.txt"; "crash.exe"; "twin.stn"; "corrupt.stn"; module_name ^ ".stn" ];
    (* the files this run made, and nothing else: next to the input only the ones it made *)
    (match !candidate_dir with
     | None -> List.iter (fun n -> try Sys.remove (Filename.concat tmp (n ^ ".stn")) with Sys_error _ -> ()) [ "shrink"; "orig" ]
     | Some _ -> List.iter (fun p -> try Sys.remove p with Sys_error _ -> ()) !candidates_made);
    try Unix.rmdir tmp with Unix.Unix_error _ -> ()
  in
  (* whatever ends the run, an exit in the middle of a check or an exception, the files it made go *)
  at_exit cleanup;
  (match !reduce with
   | Some file ->
       let text = read_file file in
       (* the program may import what is next to it. A program split across a module, which is the text of
          one that the fuzzer made, brings its module with it, and it is written in the scratch directory *)
       if not (is_split text) then begin
         single_file := true;
         candidate_dir := Some (Filename.dirname file);
         try ignore (candidate_path tmp "orig")
         with Unix.Unix_error (e, _, _) ->
           Printf.eprintf "fuzz: cannot write next to %s, where what it imports is: %s\n" file (Unix.error_message e);
           cleanup ();
           exit 2
       end;
       let still_fails =
         match (!keeping, !rejected) with
         | _, _ when !keeping_match <> None ->
             still_has starnite tmp (Match (Option.get !keeping_match, !match_arms) :: List.map (fun t -> Line t) !keeping)
         | _ :: _, _ -> still_has starnite tmp (List.map (fun t -> Line t) !keeping)
         | [], Some code -> still_rejected starnite tmp code
         | [], None -> (
             let p = candidate_path tmp "orig" in
             match differential starnite tmp p text with
             | `Differ (ri, _, rc, _) -> still_differs starnite tmp (`Differ (ri, rc))
             | `Twin (ri, _, rt, _) -> still_differs starnite tmp (`Twin (ri, rt))
             | _ ->
                 prerr_endline "fuzz: the program does not fail: nothing to reduce";
                 cleanup ();
                 exit 2
             | exception Hang what ->
                 Printf.eprintf "fuzz: '%s' timed out on the program: nothing to reduce\n" what;
                 cleanup ();
                 exit 2)
       in
       let small, evals = shrink ~budget:!budget ~still_fails text in
       Printf.eprintf "reduced %d lines to %d, in %d checks\n%!" (Array.length (lines_of text)) (Array.length (lines_of small)) evals;
       print_string small;
       cleanup ();
       exit 0
   | None -> ());
  Printf.printf "seed %d\n%!" seed;
  let failures = ref 0 and shrunk = ref 0 in
  let neg_total = ref 0 and neg_kinds : (string, int) Hashtbl.t = Hashtbl.create 16 and neg_ctx : (string, int) Hashtbl.t = Hashtbl.create 16 in
  let save case suffix prog =
    match !keep with
    | Some dir ->
        (try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
        Out_channel.with_open_bin (Filename.concat dir (sprintf "case%d%s.stn" case suffix)) (fun oc -> output_string oc prog);
        (* a program split across a module: the text is the program in one file, and its two files are here *)
        if is_split prog then begin
          let sub = Filename.concat dir (sprintf "case%d%s.split" case suffix) in
          (try Unix.mkdir sub 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
          write_program (Filename.concat sub "main.stn") prog
        end
    | None -> ()
  in
  if !crash_mode then begin
    (* the compiler has the time of a check to end, and a program that loops is not its fault *)
    time_limit := 30.0;
    let crashes = ref 0 and tried = ref 0 and shrunk = ref 0 in
    for i = 0 to !count - 1 do
      let case = seed + i in
      let prog = program case in
      let path = Filename.concat tmp "corrupt.stn" in
      for k = 0 to !corruptions - 1 do
        let rng = Random.State.make [| case; k; 0x6372 |] in
        let text = corrupt rng prog in
        (* now and then a second change: the first may leave nothing wrong *)
        let text = if Random.State.int rng 3 = 0 then corrupt rng text else text in
        incr tried;
        match crash_of starnite tmp path text with
        | None -> ()
        | Some (kind, out) ->
            incr crashes;
            Printf.printf "case %d, corruption %d: the compiler crashed %s:\n  %s\n%!" case k
              (match kind with
               | At_check | At_check_hung -> "in the check"
               | At_run args | At_run_hung args -> "in " ^ String.concat " " args)
              (String.concat "\n  " (String.split_on_char '\n' (tail out 300)));
            let suffix = sprintf ".k%d.crash" k in
            save case suffix text;
            if !shrink_failures && !shrunk < 3 then begin
              incr shrunk;
              let small, evals = shrink ~budget:!budget ~still_fails:(still_crashes starnite tmp kind) text in
              (* the shrink runs under a shorter limit than the campaign: what it ends with must fail in the same way
                 under the campaign's own, or the program that was found is what is kept *)
              let small = if still_crashes starnite tmp kind small then small else text in
              Printf.printf "  shrunk from %d lines to %d, in %d checks\n%!" (Array.length (lines_of text)) (Array.length (lines_of small)) evals;
              save case (suffix ^ ".min") small
            end
      done
    done;
    cleanup ();
    Printf.printf "%d corruptions of %d programs: %d crashes\n" !tried !count !crashes;
    exit (if !crashes > 0 then 1 else 0)
  end;
  for i = 0 to !count - 1 do
    let case = seed + i in
    let prog = program case in
    let path = Filename.concat tmp (sprintf "fuzz%d.stn" i) in
    write_program path prog;
    let failed =
      match
        if !differential_runs then differential starnite tmp path prog
        else
          match run starnite tmp [ "check" ] path with
          | 127, oi -> prerr_string oi; exit 2
          | 0, _ -> `Agreed
          | _, oi -> `Rejected oi
      with
      | `Agreed -> false
      | `Rejected oi ->
          Printf.printf "case %d: the generator produced a program the checker rejects:\n%s\n%!" case oi;
          true
      | `Differ (ri, out_i, rc, out_c) ->
          Printf.printf "case %d: interpreter (exit %d) and C (exit %d) differ\n" case ri rc;
          (match first_difference out_i out_c with
           | Some (a, b) -> Printf.printf "  interp: %s\n  c:      %s\n%!" a b
           | None -> Printf.printf "  interp tail: %S\n  c tail:      %S\n%!" (tail out_i 200) (tail out_c 200));
          if !shrink_failures && !shrunk < 3 then begin
            incr shrunk;
            save case "" prog;
            let small, evals = shrink ~budget:!budget ~still_fails:(still_differs starnite tmp (`Differ (ri, rc))) prog in
            Printf.printf "  shrunk from %d lines to %d, in %d checks\n%!" (Array.length (lines_of prog)) (Array.length (lines_of small)) evals;
            save case ".min" small
          end;
          true
      | `Twin (ri, out_i, rt, out_t) ->
          Printf.printf "case %d: the program split across a module (exit %d) and the same program in one file (exit %d) differ\n" case ri rt;
          (match
             (match first_difference (without_places out_i) (without_places out_t) with
              | Some d -> Some d
              | None -> first_difference out_i out_t)
           with
           | Some (a, b) -> Printf.printf "  split:    %s\n  one file: %s\n%!" a b
           | None -> Printf.printf "  split tail:    %S\n  one file tail: %S\n%!" (tail out_i 200) (tail out_t 200));
          if !shrink_failures && !shrunk < 3 then begin
            incr shrunk;
            save case "" prog;
            let small, evals = shrink ~budget:!budget ~still_fails:(still_differs starnite tmp (`Twin (ri, rt))) prog in
            Printf.printf "  shrunk from %d lines to %d, in %d checks\n%!" (Array.length (lines_of prog)) (Array.length (lines_of small)) evals;
            save case ".min" small
          end;
          true
      | exception Hang what ->
          (* a hang is a failure too; keep the program that caused it *)
          Printf.printf "case %d: '%s' timed out\n%!" case what;
          true
    in
    if failed then begin
      incr failures;
      save case "" prog
    end
    else if !negative then begin
      (* one mutation with a known violation: the compiler must reject it with the code that goes with it *)
      let m, text, in_context, essential = mutate case prog in
      let name = m.kind and expect = m.expect in
      let count tbl = Hashtbl.replace tbl name (1 + (try Hashtbl.find tbl name with Not_found -> 0)) in
      incr neg_total;
      count neg_kinds;
      if in_context then count neg_ctx;
      write_program path text;
      (* a failing mutation is kept, with the lines it put in the program; --shrink reduces it, keeping those
         lines if it was accepted, or the wrong code if it was rejected with one *)
      let added = List.filter (fun l -> not (blank l)) (added_lines (lines_of prog) (lines_of text)) in
      let fail ?(still_fails = fun _ -> false) ?(can_shrink = false) () =
        List.iter (fun l -> Printf.printf "  + %s\n" (String.trim l)) added;
        flush stdout;
        incr failures;
        save case ".neg" text;
        if can_shrink && !shrink_failures && !shrunk < 3 then begin
          incr shrunk;
          let small, evals = shrink ~budget:!budget ~still_fails text in
          Printf.printf "  shrunk from %d lines to %d, in %d checks\n%!" (Array.length (lines_of text)) (Array.length (lines_of small)) evals;
          save case ".neg.min" small
        end
      in
      match run starnite tmp [ "check"; "--json" ] path with
      | exception Hang what ->
          Printf.printf "case %d: '%s' timed out on the mutation '%s'\n%!" case what name;
          fail ()
      | 0, _ ->
          Printf.printf "case %d: the mutation '%s' was accepted; it should be rejected with %s\n%!" case name (show_expect expect);
          (* kept by the lines it added and the lines of the program that it needs: the match, for an arm that was taken away *)
          let keep = List.map (fun l -> Line (String.trim l)) added @ essential in
          fail ~can_shrink:(keep <> []) ~still_fails:(still_has starnite tmp keep) ()
      | _, out -> (
          match json_code out with
          | Some code when expected_ok expect code -> ()
          | got ->
              Printf.printf "case %d: the mutation '%s' was rejected with %s; it should be %s\n  %s\n%!" case name
                (match got with Some c -> c | None -> "no code") (show_expect expect) (tail out 300);
              (match got with
               | Some code -> fail ~can_shrink:true ~still_fails:(still_rejected starnite tmp code) ()
               | None -> fail ()))
    end;
    Sys.remove path
  done;
  cleanup ();
  if !negative then begin
    Printf.printf "%d mutations, each of them with a violation:\n" !neg_total;
    List.iter
      (fun m ->
        let n = try Hashtbl.find neg_kinds m.kind with Not_found -> 0 in
        let c = try Hashtbl.find neg_ctx m.kind with Not_found -> 0 in
        Printf.printf "  %-42s %3d, %3d made of the program's own lines\n" m.kind n c)
      mutations
  end;
  Printf.printf "%d of %d agreed\n" (!count - !failures) !count;
  exit (if !failures > 0 then 1 else 0)
