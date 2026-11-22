(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Differential program fuzzer (section 21.2), first cut. Its programs use trait values
   (any Fig, any Chk, any Show): boxing, calls through method tables, arrays and nested
   values of them, closures that capture them, mut parameters and failures that cross a
   trait method.

   Builds well-typed programs by construction: it picks a type, then a production that
   yields that type, tracking which variables are live and mutable. Each program runs
   on the reference interpreter and on the debug C build; the outputs and exit
   statuses must match, and the debug runtime must report balanced counts.

     dune exec tests/fuzz/fuzz.exe -- [--count N] [--seed S] [--keep DIR]
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
            match int g 4 with
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
  let deadline = Unix.gettimeofday () +. 120.0 in
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

let () =
  let count = ref 50 and seed = ref None and keep = ref None and print_only = ref false in
  Arg.parse
    [ ("--count", Arg.Set_int count, "N  number of programs (default 50)");
      ("--print", Arg.Set print_only, "  print the program of the seed given by --seed and stop");
      ("--seed", Arg.Int (fun s -> seed := Some s), "S  first seed (default random)");
      ("--keep", Arg.String (fun d -> keep := Some d), "DIR  save failing programs in DIR") ]
    (fun a -> raise (Arg.Bad ("unexpected argument " ^ a)))
    "usage: fuzz.exe [--count N] [--seed S] [--keep DIR]";
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
    print_string (program seed);
    exit 0
  end;
  Printf.printf "seed %d\n%!" seed;
  let tmp = Filename.concat (Filename.get_temp_dir_name ()) (sprintf "starnite-fuzz-%d-%08x" (Unix.getpid ()) (Random.bits ())) in
  Unix.mkdir tmp 0o700;
  let failures = ref 0 in
  for i = 0 to !count - 1 do
    let case = seed + i in
    let prog = program case in
    let path = Filename.concat tmp (sprintf "fuzz%d.stn" i) in
    Out_channel.with_open_bin path (fun oc -> output_string oc prog);
    let failed =
      match
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
          true
      | exception Hang what ->
          (* a hang is a failure too; keep the program that caused it *)
          Printf.printf "case %d: '%s' timed out\n%!" case what;
          true
    in
    if failed then begin
      incr failures;
      match !keep with
      | Some dir ->
          (try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
          Out_channel.with_open_bin (Filename.concat dir (sprintf "case%d.stn" case)) (fun oc -> output_string oc prog)
      | None -> ()
    end;
    Sys.remove path
  done;
  (try Sys.remove (Filename.concat tmp "out.txt") with Sys_error _ -> ());
  (try Unix.rmdir tmp with Unix.Unix_error _ -> ());
  Printf.printf "%d of %d agreed\n" (!count - !failures) !count;
  exit (if !failures > 0 then 1 else 0)
