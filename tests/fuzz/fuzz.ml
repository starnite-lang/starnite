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

   A failing program is shrunk, by taking out statements and items and simplifying what
   is left, while it still fails the same way.

     dune exec tests/fuzz/fuzz.exe -- [--count N] [--seed S] [--keep DIR] [--shrink]
     dune exec tests/fuzz/fuzz.exe -- --reduce FILE [--keeping TEXT | --rejected CODE]

   tests/fuzz/selftest.sh checks the fuzzer itself, with the compilers of buggy.sh.
*)

let sprintf = Printf.sprintf

let types = [| "Int"; "Bool"; "Str"; "Array[Int]"; "Pair"; "Shape"; "Int?"; "any Show"; "Array[any Show]" |]

(* Trait values have no Show of their own, so they are never printed directly: [types]
   are the printable ones, [all_types] also hold variables and parameters. *)
let any_types = [| "any Fig"; "Array[any Fig]"; "(any Fig)?"; "any Chk" |]
let all_types = Array.append types any_types

let prelude =
  {|fn no_int() -> Int?:
    None

fn no_ints() -> Array[Int]:
    []

type Pair = struct(a: Int, b: Str)
type Shape = Dot | Box(w: Int, h: Int) | Named(name: Str, inner: Array[Int])

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

(* ---------- the generator ---------- *)

type gen = {
  rng : Random.State.t;
  mutable scopes : (string * string * bool) list list;   (* name, type, mutable *)
  mutable n : int;
  mutable fns : (string * string list) list;              (* functions returning Int *)
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

let leaf g t =
  match t with
  | "Int" -> small g
  | "Bool" -> choice g [| "true"; "false" |]
  | "Str" -> choice g [| {|"a"|}; {|"bc"|}; {|""|}; {|"héllo"|}; {|"0123456789abcdef"|} |]
  | "Array[Int]" -> choice g [| "no_ints()"; "[1]"; "[3, 1, 2]" |]
  | "Pair" -> {|Pair(0, "p")|}
  | "Shape" -> "Dot"
  | "Int?" -> "no_int()"
  | "any Show" -> choice g [| "Pair(0, \"p\")"; "7"; "true"; "Dot" |]
  | "Array[any Show]" -> "no_shows()"
  | "any Fig" -> choice g [| "Sq(1)"; "Rc(2, 3)"; "Tri(4)" |]
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
        match int g 5 with
        | 0 -> sprintf "(%s < %s)" (e "Int") (e "Int")
        | 1 -> sprintf "(%s == %s)" (e "Str") (e "Str")
        | 2 -> sprintf "(%s and %s)" (e "Bool") (e "Bool")
        | 3 -> sprintf "(not %s)" (e "Bool")
        | _ -> sprintf "(%s == %s)" (e "Array[Int]") (e "Array[Int]"))
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
        match int g 4 with
        | 0 -> "[" ^ String.concat ", " (List.init (range g 1 4) (fun _ -> e "Int")) ^ "]"
        | 1 -> sprintf "[x +%% %s for x in %s]" (small g) (e "Array[Int]")
        | 2 -> sprintf "[i *%% i for i in 0..%d]" (int g 6)
        | _ -> sprintf "filled(%d, %s)" (int g 4) (e "Int"))
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
        match int g 11 with
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
  let k = int g 15 in
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
            match int g 4 with
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
        head :: with_scope g [ (n, "Int", false) ] (fun () -> stmts g (ind + 1) (range g 1 3) (d - 1))
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
        head
        :: with_scope g [ (n, "any Fig", false) ] (fun () ->
               [ sprintf "%s    print(describe(%s))" p n; sprintf {|%s    print(f"{%s.scale(%s)}")|} p n (small g) ]
               @ stmts g (ind + 1) 1 (d - 1))
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
            match int g 5 with
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
    | _ -> [ sprintf "%sprint(%s)" p (if chance g 0.5 then sprintf "describe(%s)" (expr g "any Fig" 2) else expr g "Str" 3) ]

let program seed =
  let g = { rng = Random.State.make [| seed |]; scopes = [ [] ]; n = 0; fns = [] } in
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
  String.concat "\n" ((prelude :: List.concat fns) @ ("fn main():" :: main) @ [ {|    print("end")|} ]) ^ "\n"

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

(* the generated part of the program starts after the prelude, which is the same in every program *)
let generated_from () = Array.length (lines_of prelude)

(* a violation in lines of its own goes before the last print of main, a function of its own before main *)
let before_end lines news =
  let r = ref (Array.length lines - 1) in
  Array.iteri (fun i l -> if l = {|    print("end")|} then r := i) lines;
  insert_after lines (!r - 1) news

let before_main lines news = insert_after lines (main_index lines - 1) news

(* the declarations `let|var NAME: TYPE = ...` of the generated part of the program, at any depth: a
   statement put right after one, with its indentation, is in the scope of the name *)
let decls lines =
  let first = generated_from () in
  let r = ref [] in
  Array.iteri (fun i l -> if i >= first then match decl_of l with Some (ind, v, n, t) -> r := (i, ind, v, n, t) :: !r | None -> ()) lines;
  List.rev !r

(* the lines of the generated part that are whole statements of a body: a statement put after one,
   with its indentation, goes in the same block. A header, an arm (with its body on the same line or
   not), and the result that ends a function are not among them. *)
let statement_lines lines =
  let first = generated_from () in
  let r = ref [] in
  Array.iteri
    (fun i l ->
      let t = String.trim l in
      if i >= first && indent_of l >= 4 && t <> "" && t.[0] <> '(' && (not (ends_with ":" t)) && not (contains t "->") then
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

(* One violation of a rule of the language. [in_context] puts it next to a line or a variable of the
   program, and is [None] when the program has none that fits; with the program it gives the lines it
   needs that were there already, which a reduction of the program has to keep for the violation to
   stay. [own] writes it with a variable of its own, anywhere, in one of the ways it has, so that every
   kind is exercised whatever the program has. *)
type mutation = {
  kind : string;
  expect : expect;
  in_context : Random.State.t -> string array -> (string array * string list) option;
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
          let first = generated_from () in
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
              Some (insert_after (insert_after lines j [ take ]) (j - 1) [ at (indent_of lines.(j)) "let neg_s: Str = \"x\"" ], [ String.trim lines.(j) ])
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
              Some (delete_lines lines i (group_at lines i), [ String.trim lines.(!h) ])
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
      if blank !cur.(!i) then incr i
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

(* Run the compiler on a file, with its output in a temporary file and a time limit. *)
let run starnite tmp args path : int * string =
  let out = Filename.concat tmp "out.txt" in
  let fd = Unix.openfile out [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
  (* the compiler runs the program it builds as a child of its own, so each invocation
     gets a process group of its own, and the whole group is killed afterwards *)
  let argv = Array.of_list ((starnite :: args) @ [ path ]) in
  let pid =
    match Unix.fork () with
    | 0 -> (
        try
          ignore (Unix.setsid ());
          Unix.dup2 fd Unix.stdout;
          Unix.dup2 fd Unix.stderr;
          (* execvp searches PATH, so STARNITE may name an installed command *)
          Unix.execvp starnite argv
        with e ->
          prerr_string (sprintf "fuzz: cannot run %s: %s\n" starnite (Printexc.to_string e));
          flush stderr;
          Unix._exit 127)
    | pid -> pid
  in
  Unix.close fd;
  let kill_group () = try Unix.kill (-pid) Sys.sigkill with Unix.Unix_error _ -> () in
  let deadline = Unix.gettimeofday () +. !time_limit in
  let rec wait () =
    match Unix.waitpid [ Unix.WNOHANG ] pid with
    | 0, _ ->
        if Unix.gettimeofday () > deadline then begin
          kill_group ();
          ignore (Unix.waitpid [] pid);
          raise (Hang (String.concat " " args))
        end;
        Unix.sleepf 0.01;
        wait ()
    | _, Unix.WEXITED c -> c
    | _, (Unix.WSIGNALED s | Unix.WSTOPPED s) -> 128 + abs s
  in
  let code = wait () in
  (* nothing the invocation started may outlive it and write to the next case's output *)
  kill_group ();
  (code, read_file out)

let tail s n = if String.length s <= n then s else String.sub s (String.length s - n) n

let first_difference a b =
  let rec go = function
    | x :: xs, y :: ys -> if x <> y then Some (x, y) else go (xs, ys)
    | _ -> None
  in
  go (String.split_on_char '\n' a, String.split_on_char '\n' b)

(* what makes a program fail the same way: it checks, and the interpreter and the C build end with the
   statuses they ended with, and still disagree *)
let differential starnite tmp path =
  let ci, oi = run starnite tmp [ "check" ] path in
  if ci = 127 then begin
    (* the compiler did not start at all: no case can be judged *)
    prerr_string oi;
    exit 2
  end;
  if ci <> 0 then `Rejected oi
  else
    let ri, out_i = run starnite tmp [ "run"; "--interp" ] path in
    let rc, out_c = run starnite tmp [ "run" ] path in
    if ri = rc && out_i = out_c then `Agreed else `Differ (ri, out_i, rc, out_c)

let still_differs starnite tmp (ri0, rc0) text =
  let p = Filename.concat tmp "shrink.stn" in
  Out_channel.with_open_bin p (fun oc -> output_string oc text);
  match differential starnite tmp p with
  | `Differ (ri, _, rc, _) -> ri = ri0 && rc = rc0
  | `Agreed | `Rejected _ -> false
  | exception Hang _ -> false

(* what makes a mutated program that was accepted fail the same way: it is accepted, and still has the
   lines of the violation *)
let still_has starnite tmp markers text =
  let p = Filename.concat tmp "shrink.stn" in
  Out_channel.with_open_bin p (fun oc -> output_string oc text);
  List.for_all (contains text) markers
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
  let p = Filename.concat tmp "shrink.stn" in
  Out_channel.with_open_bin p (fun oc -> output_string oc text);
  match run starnite tmp [ "check"; "--json" ] p with
  | 0, _ -> false
  | _, out -> json_code out = Some code
  | exception Hang _ -> false

let () =
  let count = ref 50 and seed = ref None and keep = ref None and print_only = ref false in
  let shrink_failures = ref false and reduce = ref None and keeping = ref [] and rejected = ref None and budget = ref 400 in
  let negative = ref true and differential_runs = ref true and print_mutated = ref false in
  Arg.parse
    [ ("--count", Arg.Set_int count, "N  number of programs (default 50)");
      ("--print", Arg.Set print_only, "  print the program of the seed given by --seed and stop");
      ("--mutated", Arg.Set print_mutated, "  with --print: print its mutation instead, the kind and the code it must be rejected with on stderr");
      ("--seed", Arg.Int (fun s -> seed := Some s), "S  first seed (default random)");
      ("--keep", Arg.String (fun d -> keep := Some d), "DIR  save failing programs in DIR");
      ("--shrink", Arg.Set shrink_failures, "  shrink each failing program (at most three), saving caseN.min.stn in the --keep directory");
      ("--shrink-budget", Arg.Set_int budget, "N  how many checks a shrink may make (default 400)");
      ("--reduce", Arg.String (fun f -> reduce := Some f), "FILE  shrink the failing program in FILE, print the result, and stop");
      ("--keeping", Arg.String (fun t -> keeping := !keeping @ [ t ]), "TEXT  with --reduce: keep what compiles and contains TEXT (more than once: all of them), instead of what fails (for a mutation that was accepted)");
      ("--rejected", Arg.String (fun c -> rejected := Some c), "CODE  with --reduce: keep what the checker rejects with CODE (for a mutation rejected with the wrong code)");
      ("--no-negative", Arg.Clear negative, "  do not mutate programs to be rejected");
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
    if !print_mutated then begin
      let m, text, in_context, _ = mutate seed prog in
      Printf.eprintf "%s, to be rejected with %s%s\n" m.kind (show_expect m.expect) (if in_context then ", made of the program's own lines" else "");
      print_string text
    end
    else print_string prog;
    exit 0
  end;
  let tmp = Filename.concat (Filename.get_temp_dir_name ()) (sprintf "starnite-fuzz-%d-%08x" (Unix.getpid ()) (Random.bits ())) in
  Unix.mkdir tmp 0o700;
  let cleanup () =
    List.iter (fun f -> try Sys.remove (Filename.concat tmp f) with Sys_error _ -> ()) [ "out.txt"; "shrink.stn" ];
    try Unix.rmdir tmp with Unix.Unix_error _ -> ()
  in
  (match !reduce with
   | Some file ->
       let text = read_file file in
       let still_fails =
         match (!keeping, !rejected) with
         | _ :: _, _ -> still_has starnite tmp !keeping
         | [], Some code -> still_rejected starnite tmp code
         | [], None -> (
             let p = Filename.concat tmp "orig.stn" in
             Out_channel.with_open_bin p (fun oc -> output_string oc text);
             match differential starnite tmp p with
             | `Differ (ri, _, rc, _) -> still_differs starnite tmp (ri, rc)
             | _ ->
                 prerr_endline "fuzz: the program does not fail: nothing to reduce";
                 cleanup ();
                 exit 2)
       in
       let small, evals = shrink ~budget:!budget ~still_fails text in
       Printf.eprintf "reduced %d lines to %d, in %d checks\n%!" (Array.length (lines_of text)) (Array.length (lines_of small)) evals;
       print_string small;
       (try Sys.remove (Filename.concat tmp "orig.stn") with Sys_error _ -> ());
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
        Out_channel.with_open_bin (Filename.concat dir (sprintf "case%d%s.stn" case suffix)) (fun oc -> output_string oc prog)
    | None -> ()
  in
  for i = 0 to !count - 1 do
    let case = seed + i in
    let prog = program case in
    let path = Filename.concat tmp (sprintf "fuzz%d.stn" i) in
    Out_channel.with_open_bin path (fun oc -> output_string oc prog);
    let failed =
      match
        if !differential_runs then differential starnite tmp path
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
            let small, evals = shrink ~budget:!budget ~still_fails:(still_differs starnite tmp (ri, rc)) prog in
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
      Out_channel.with_open_bin path (fun oc -> output_string oc text);
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
          (* with nothing added (an arm taken away) there is nothing to keep it by *)
          fail ~can_shrink:(added <> []) ~still_fails:(still_has starnite tmp (List.map String.trim added @ essential)) ()
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
