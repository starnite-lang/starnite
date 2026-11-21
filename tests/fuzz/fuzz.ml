(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Differential program fuzzer (section 21.2), first cut.

   Builds well-typed programs by construction: it picks a type, then a production that
   yields that type, tracking which variables are live and mutable. Each program runs
   on the reference interpreter and on the debug C build; the outputs and exit
   statuses must match, and the debug runtime must report balanced counts.

     dune exec tests/fuzz/fuzz.exe -- [--count N] [--seed S] [--keep DIR]
*)

let sprintf = Printf.sprintf

let types = [| "Int"; "Bool"; "Str"; "Array[Int]"; "Pair"; "Shape"; "Int?" |]

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
  | _ -> invalid_arg t

let rec expr g t d =
  let vs = vars_of g t in
  if vs <> [] && chance g 0.45 then choice_l g vs
  else if d <= 0 then leaf g t
  else
    let e t' = expr g t' (d - 1) in
    match t with
    | "Int" -> (
        match int g 9 with
        | 0 -> sprintf "(%s +%% %s)" (e "Int") (e "Int")
        | 1 -> sprintf "(%s -%% %s)" (e "Int") (e "Int")
        | 2 -> sprintf "(%s *%% %s)" (e "Int") (small g)
        | 3 -> sprintf "len(%s)" (e "Array[Int]")
        | 4 -> sprintf "len(%s)" (e "Str")
        | 5 -> sprintf "(if %s: %s else: %s)" (e "Bool") (e "Int") (e "Int")
        | 6 -> sprintf "%s.a" (e "Pair")
        | 7 -> sprintf "(%s).or(%s)" (e "Int?") (small g)
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
        match int g 4 with
        | 0 -> sprintf "(%s + %s)" (e "Str") (e "Str")
        | 1 -> sprintf {|f"<{%s}|{%s}>"|} (e "Int") (e (choice g types))
        | 2 -> sprintf "%s.b" (e "Pair")
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
  let k = int g 10 in
  let fallback () = [ sprintf "%sprint(%s)" p (leaf g "Str") ] in
  if k <= 1 || d <= 0 then begin
    let t = choice g types in
    let n = fresh g "v" in
    let mut = chance g 0.5 in
    let line = sprintf "%s%s %s: %s = %s" p (if mut then "var" else "let") n t (expr g t 3) in
    declare g (n, t, mut);
    [ line ]
  end
  else
    match k with
    | 2 -> (
        let t = choice g types in
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
    | _ -> (
        match vars_of ~mutable_:true g "Int" with
        | [] -> fallback ()
        | vs ->
            let v = choice_l g vs in
            [ sprintf "%svar %s = 0" p (fresh g "c"); sprintf "%swhile %s > 0 and %s < 50:" p v v;
              sprintf "%s    %s = %s +%% 7" p v v ])

let program seed =
  let g = { rng = Random.State.make [| seed |]; scopes = [ [] ]; n = 0; fns = [] } in
  let fns =
    List.init (int g 3) (fun _ ->
        let name = fresh g "f" in
        let ps = List.init (int g 3) (fun _ -> choice g [| "Int"; "Str"; "Array[Int]" |]) in
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
          Unix.execv starnite argv
        with _ -> Unix._exit 127)
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
  let count = ref 50 and seed = ref None and keep = ref None in
  Arg.parse
    [ ("--count", Arg.Set_int count, "N  number of programs (default 50)");
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
  let seed = match !seed with Some s -> s | None -> Random.int (1 lsl 30) in
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
