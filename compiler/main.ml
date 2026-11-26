(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* The starnite command (section 19.5). *)

open Syntax

let usage =
  {|usage: starnite <command> [options] <file.stn>

commands:
  run <file>      compile and run (add --interp to use the reference interpreter)
  build <file>    compile to an executable next to the source (or -o <path>)
  check <file>    check without generating code
  test <file>     run the test blocks of a file, and check the budgets of its bench blocks
  bench <file>    run the bench blocks of a file: counters, then times
  emit-c <file>   print the generated C

options:
  --interp        run with the reference interpreter (section 21.1)
  --release       build with -O2 instead of the debug runtime
  --json          print diagnostics as JSON (section 19.4)
  -o <path>       output path for build
  --cc <cmd>      C compiler to use (default: $CC or cc)
  --keep-c        keep the generated C file
  --explain-copies  list where a write may copy a shared value, and where a loop raises a count
  --profile-copies  count those at run time and print the totals when the program ends
  --cases <n>     inputs each property test is run on (default 100)
  --seed <n>      the seed of the inputs, as a failing property test printed it
  --update-snapshots  accept what assert_snapshot now gives as the stored copy
|}

let json = ref false

let read_file f = In_channel.with_open_bin f In_channel.input_all

let source_line file line =
  try
    let src = if file = "<prelude>" then Runtime_src.prelude else read_file file in
    let lines = String.split_on_char '\n' src in
    if line >= 1 && line <= List.length lines then Some (List.nth lines (line - 1)) else None
  with _ -> None

let json_escape s =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

(* Error format of section 19.1. *)
let report code (l : loc) msg =
  let severity = if code <> "" && code.[0] = 'W' then "warning" else "error" in
  (* a message without a code: valid code that a backend does not support yet *)
  let header = if code = "" then severity else Printf.sprintf "%s[%s]" severity code in
  if !json then
    Printf.eprintf "{\"severity\":\"%s\",\"code\":\"%s\",\"message\":\"%s\",\"file\":\"%s\",\"line\":%d,\"col\":%d}\n"
      severity code (json_escape msg) (json_escape l.file) l.line l.col
  else begin
    Printf.eprintf "%s: %s\n" header msg;
    if l.line > 0 && l.line < max_int then begin
      Printf.eprintf "  --> %s:%d:%d\n" l.file l.line l.col;
      match source_line l.file l.line with
      | Some text ->
          let num = string_of_int l.line in
          let pad = String.make (String.length num) ' ' in
          Printf.eprintf "%s |\n%s | %s\n%s | %s^\n" pad num text pad (String.make (max 0 (l.col - 1)) ' ')
      | None -> ()
    end else Printf.eprintf "  --> %s\n" l.file
  end

let load_prelude () =
  Parser.allow_bodiless := true;
  let p = Parser.parse_file "<prelude>" Runtime_src.prelude in
  Parser.allow_bodiless := false;
  p

let trap_exit kind (l : loc) msg =
  Interp.flush_out ();
  Printf.eprintf "trap: %s at %s:%d:%d\n%s\n" kind l.file l.line l.col msg;
  exit 2

let run_interp (prog : Types.tprog) =
  match prog.main with
  | None -> prerr_endline "error: no main function"; exit 1
  | Some m -> (
      let env = { Interp.prog; vars = Hashtbl.create 16; sub = [] } in
      try
        ignore (Interp.call_fn env m [] [] noloc);
        Interp.flush_out ();
        exit 0
      with
      | Interp.Failed (t, v) ->
          Interp.flush_out ();
          Printf.eprintf "error: %s\n" (Interp.show_value env t v);
          exit 1
      | Values.Trap (kind, l, msg) -> trap_exit kind l msg
      | Stack_overflow ->
          (* the C build reports the same, from a handler of the fault *)
          Interp.flush_out ();
          prerr_string "trap: stack overflow\nthe program recursed deeper than its stack allows\n";
          exit 2
      (* the same report as the C backend's trap for a failed assert *)
      | Interp.Assert_failed (_, l) -> trap_exit "assertion failed" l "assert")

(* Doc tests (section 20.2). In a doc comment, which starts with ##, a line `>>> expr` is run and
   the lines after it, up to a blank one or the end of the comment, are what Show must give for
   its value. Each becomes a test at the end of the module, where it sees the module's private
   items: `assert f"{expr}" == "expected"`. *)
let doc_tests (src : string) : string =
  let lines = Array.of_list (String.split_on_char '\n' src) in
  let doc l = let t = String.trim l in if String.length t >= 2 && String.sub t 0 2 = "##" then Some (String.sub t 2 (String.length t - 2)) else None in
  let quote text =
    let b = Buffer.create (String.length text + 2) in
    String.iter (fun ch -> match ch with
        | '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\" | '\n' -> Buffer.add_string b "\\n"
        | ch -> Buffer.add_char b ch) text;
    Buffer.contents b in
  let out = Buffer.create 256 in
  let n = Array.length lines in
  let i = ref 0 in
  while !i < n do
    (match doc lines.(!i) with
     | Some body when (let t = String.trim body in String.length t > 3 && String.sub t 0 3 = ">>>") ->
         let t = String.trim body in
         let expr = String.trim (String.sub t 3 (String.length t - 3)) in
         (* the expected lines keep what indentation they have beyond that of the >>> line *)
         let indent = let k = ref 0 in while !k < String.length body && body.[!k] = ' ' do incr k done; !k in
         let at = !i + 1 in
         let expected = ref [] in
         let j = ref (!i + 1) in
         let stop = ref false in
         while not !stop && !j < n do
           (match doc lines.(!j) with
            | Some b when String.trim b <> "" && not (let t = String.trim b in String.length t >= 3 && String.sub t 0 3 = ">>>") ->
                let cut = min indent (String.length b) in
                let cut = if String.trim (String.sub b 0 cut) = "" then cut else 0 in
                expected := String.sub b cut (String.length b - cut) :: !expected; incr j
            | _ -> stop := true)
         done;
         Printf.bprintf out "\ntest \"doc line %d: %s\":\n    assert f\"{%s}\" == \"%s\"\n" at (quote expr) expr
           (quote (String.concat "\n" (List.rev !expected)));
         i := !j
     | _ -> incr i)
  done;
  Buffer.contents out

(* Bench blocks (section 20.3).

       bench "name" for n in [10, 100] budget allocs <= 4 budget copies == 0:
           setup
           measure:
               work

   A bench is turned into a function before the file is parsed. Its first line becomes the head of
   a function, which takes n when there is a `for`. Its `measure:` line becomes three: a let of
   the limits of its budgets, worked out once, there, where the setup before it can be used; a
   call of bench_begin with them, which starts the counters or the clock; and the loop that the
   runtime ends, `while bench_running():`, whose condition evaluates nothing. Positions stay
   those of the file: the lines put in are reported as the `measure:` line (the second value
   returned says which line each line of the new text is). The calls of those functions make up
   a main of their own, which
   takes the place of the program's for `starnite bench` and for the budget checks of
   `starnite test`. In any other build the functions are checked like the rest and never run.

   Returns the new text, the line to report for each of its lines, and the body of that main;
   raises Error on a bench it cannot read. *)
let bench_blocks file (src : string) : string * int array * string list =
  let lines = Array.of_list (String.split_on_char '\n' src) in
  let n = Array.length lines in
  let calls = ref [] and count = ref 0 in
  let bad i fmt = Printf.ksprintf (fun m -> raise (Error ("E0100", { file; line = i + 1; col = 1 }, m))) fmt in
  let starts p t = String.length t >= String.length p && String.sub t 0 (String.length p) = p in
  (* the first place sub stands in t at or after from *)
  let find t sub from =
    let k = String.length sub and len = String.length t in
    let rec go i = if i + k > len then None else if String.sub t i k = sub then Some i else go (i + 1) in
    go from in
  for i = 0 to n - 1 do
    let line = lines.(i) in
    if starts "bench \"" line then begin
      (* the name, as a string literal *)
      let close =
        let rec go j = if j >= String.length line then bad i "the name of this bench does not end" else if line.[j] = '\\' then go (j + 2) else if line.[j] = '"' then j else go (j + 1) in
        go 7 in
      let name = String.sub line 6 (close - 5) in
      let rest = String.trim (String.sub line (close + 1) (String.length line - close - 1)) in
      if rest = "" || rest.[String.length rest - 1] <> ':' then bad i "a bench ends its first line with ':'";
      let rest = " " ^ String.trim (String.sub rest 0 (String.length rest - 1)) ^ " " in
      if find rest " threads " 0 <> None then bad i "`threads` on a bench arrives with tasks, in milestone 6";
      (* for IDENT in EXPR, then each budget *)
      let parts =
        let rec split from acc =
          match find rest " budget " from with
          | Some j -> split (j + 8) (String.trim (String.sub rest from (j - from)) :: acc)
          | None -> List.rev (String.trim (String.sub rest from (String.length rest - from)) :: acc) in
        split 0 [] in
      let head, budgets = match parts with h :: b -> (h, b) | [] -> ("", []) in
      let var, source =
        if head = "" then (None, "")
        else if starts "for " head then
          match find head " in " 4 with
          | Some j -> (Some (String.trim (String.sub head 4 (j - 4))), String.trim (String.sub head (j + 4) (String.length head - j - 4)))
          | None -> bad i "a bench is run for a name `in` a list: for n in [10, 100]"
        else bad i "after its name a bench has `for name in list`, then its budgets" in
      if List.length budgets > 4 then bad i "a bench has at most four budgets";
      let spec, limits =
        List.split (List.map (fun bgt ->
            let op_at = match find bgt "<" 0, find bgt "==" 0 with
              | Some a, Some b -> min a b | Some a, None -> a | None, Some b -> b
              | None, None -> bad i "a budget compares a counter with a limit: budget allocs <= 10" in
            let counter = String.trim (String.sub bgt 0 op_at) in
            let op = if starts "<=" (String.sub bgt op_at (String.length bgt - op_at)) then "<=" else if bgt.[op_at] = '<' then "<" else "==" in
            let limit = String.trim (String.sub bgt (op_at + String.length op) (String.length bgt - op_at - String.length op)) in
            if not (List.mem counter [ "allocs"; "alloc_bytes"; "copies"; "count_ops"; "time" ]) then
              bad i "'%s' is not a counter; the counters are allocs, alloc_bytes, copies and count_ops" counter;
            (* a time differs from machine to machine, and is not held to a budget *)
            (counter ^ op, if counter = "time" then "0" else limit)) budgets) in
      let limits = limits @ List.init (4 - List.length limits) (fun _ -> "0") in
      let fn = Printf.sprintf "__bench_%d" !count in
      incr count;
      lines.(i) <- Printf.sprintf "fn %s(%s) ! io:" fn (match var with Some v -> v ^ ": Int" | None -> "");
      (* its measure line, before the next line that starts at the margin *)
      let j = ref (i + 1) and found = ref false in
      while not !found && !j < n && (lines.(!j) = "" || lines.(!j).[0] = ' ' || lines.(!j).[0] = '#' || String.trim lines.(!j) = "") do
        if String.trim lines.(!j) = "measure:" then begin
          let indent = String.sub lines.(!j) 0 (String.index lines.(!j) 'm') in
          lines.(!j) <- String.concat "\n" [
              Printf.sprintf "%slet (__bench_a, __bench_b, __bench_c, __bench_d) = (%s)" indent (String.concat ", " limits);
              Printf.sprintf "%sbench_begin(%s, \"%s\", %s, \"%s\", __bench_a, __bench_b, __bench_c, __bench_d)" indent name
                (match var with Some v -> v | None -> "") (match var with Some v -> v | None -> "0") (String.concat " " spec);
              Printf.sprintf "%swhile bench_running():" indent ];
          found := true
        end;
        incr j
      done;
      if not !found then bad i "a bench has a `measure:` block, the part that is measured";
      calls := (match var with
          | Some v -> [ Printf.sprintf "    for %s in %s:" v source; Printf.sprintf "        %s(%s)" fn v ]
          | None -> [ Printf.sprintf "    %s()" fn ]) :: !calls
    end
  done;
  (* each line of the file is now one line or three: say which line of the file each came from *)
  let map = ref [ 0 ] in
  Array.iteri (fun i l -> List.iter (fun _ -> map := (i + 1) :: !map) (String.split_on_char '\n' l)) lines;
  (String.concat "\n" (Array.to_list lines), Array.of_list (List.rev !map), List.concat (List.rev !calls))

let front_end ?(docs = false) ?(bench = false) file =
  let src = read_file file in
  let src, line_map, bench_calls = bench_blocks file src in
  (* for a run of the benches, a main that calls each of them *)
  let src = if bench then src ^ "\nfn __bench_main() ! io:\n" ^ String.concat "\n" (if bench_calls = [] then [ "    print(\"no bench blocks\")" ] else bench_calls) ^ "\n" else src in
  (* the examples in doc comments are tests of the module (section 20.2) *)
  let src = if docs then src ^ doc_tests src else src in
  let pre = load_prelude () in
  (* positions are those of the file as it was written; the modules it imports are read as they are *)
  Lexer.line_map := line_map;
  let user = try Parser.parse_file file src with e -> Lexer.line_map := [||]; raise e in
  Lexer.line_map := [||];
  let user =
    if not bench then user
    else { user with items = List.filter_map (function
        | IFn f when f.fname = "main" -> None
        | IFn f when f.fname = "__bench_main" -> Some (IFn { f with fname = "main" })
        | it -> Some it) user.items } in
  let imported = Loader.load ~entry:file user in
  (user, imported, Typecheck.check_program pre imported user)

(* Where the snapshot of a test is kept: snapshots/<module>/<test>.snap beside the source, and
   <test>.2.snap for a second assert_snapshot in the same test. A name keeps its letters, digits,
   hyphens and underscores and nothing else, so it has no dot: the files of one test can never be
   those of another whose name differs, whichever snapshot of each it is. *)
let snapshot_path file test nth =
  let safe = String.map (fun ch -> match ch with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '-' | '_' -> ch | _ -> '_') test in
  let dir = Filename.concat (Filename.concat (Filename.dirname file) "snapshots") (Filename.remove_extension (Filename.basename file)) in
  (dir, Filename.concat dir (if nth = 1 then safe ^ ".snap" else Printf.sprintf "%s.%d.snap" safe nth))

let rec mkdirs d = if d <> "" && d <> "." && d <> "/" && not (Sys.file_exists d) then (mkdirs (Filename.dirname d); Unix.mkdir d 0o755)

(* starnite test: each test runs alone; a trap fails only that test (section 22.1). *)
let run_tests_interp ~cases ~seed ~update file (user : Syntax.file) imported (prog : Types.tprog) =
  let pass = ref 0 and failn = ref 0 in
  (* which test each snapshot file belongs to: two names can differ only in characters that a
     file name does not keep *)
  (* Tests that take snapshots and whose first snapshot file is the same: each is failed before
     it reads or writes anything, so that neither can overwrite the other's stored copy. *)
  let takes_snapshots (body : Types.texpr) =
    let found = ref false in
    Cgen.walk_texpr (fun (x : Types.texpr) -> match x.e with
        | Types.XCall (Types.CBuiltin ("assert_snapshot_text@Str", _), _, _) -> found := true
        | _ -> ()) (fun _ -> ()) body;
    !found in
  let snapshot_tests = List.filter_map (fun (name, body, (l : loc), _, _) ->
      if takes_snapshots body then Some (snd (snapshot_path file name 1), name, l.line) else None) prog.tests in
  let shares_snapshot name line =
    let path = snd (snapshot_path file name 1) in
    List.find_opt (fun (p, n, ln) -> p = path && (n, ln) <> (name, line)) snapshot_tests in
  List.iter
    (fun (name, body, (l : loc), inputs, cond) ->
      let env = { Interp.prog; vars = Hashtbl.create 16; sub = [] } in
      let fail_with msg =
        incr failn;
        Interp.flush_out ();
        Printf.printf "FAIL %s (%s:%d)\n     %s\n" name l.file l.line msg
      in
      (* a snapshot that is missing is written, and the test fails so that it gets read *)
      let nth = ref 0 and written = ref [] in
      Interp.snapshot := (fun text sl ->
          incr nth;
          let dir, path = snapshot_path file name !nth in
          (* a test is the one at its line: two may have the same name *)
          (match shares_snapshot name l.line with
           | Some (shared, other, line) ->
               raise (Interp.Assert_failed (Printf.sprintf "the snapshot of this test would be kept in %s, which is where that of the test \"%s\" at line %d is kept; give one of them another name" shared other line, sl))
           | None -> ());
          let write () = mkdirs dir; Out_channel.with_open_bin path (fun oc -> output_string oc text; output_char oc '\n') in
          let stored = if Sys.file_exists path then Some (In_channel.with_open_bin path In_channel.input_all) else None in
          match stored with
          | Some s when s = text ^ "\n" -> ()
          | _ when update -> write ()
          (* the test goes on, so that every snapshot it has is written in one run *)
          | None -> write (); written := path :: !written
          | Some s ->
              raise (Interp.Assert_failed
                       (Printf.sprintf "snapshot differs from %s (--update-snapshots accepts the new one)\n     stored: %s\n     now:    %s"
                          path (String.trim s) text, sl)));
      (* None when the body passes, Some why when it does not *)
      let attempt () =
        match Interp.eval env body with
        | _ | (exception Interp.Return _) ->   (* a return in a test block ends the test normally *)
            if !written = [] then None
            else Some (Printf.sprintf "snapshot written to %s; read it, then run the tests again" (String.concat ", " (List.rev !written)))
        | exception Interp.Failed (t, v) -> Some ("failed with " ^ Interp.show_value env t v)
        | exception Interp.Assert_failed (msg, al) -> Some (Printf.sprintf "%s at %s:%d:%d" msg al.file al.line al.col)
        | exception Values.Trap (kind, tl, msg) -> Some (Printf.sprintf "trap: %s at %s:%d:%d: %s" kind tl.file tl.line tl.col msg)
        | exception Stack_overflow -> Some "trap: stack overflow" in
      if inputs = [] then begin
        match attempt () with
        | None -> incr pass; Interp.flush_out (); Printf.printf "ok   %s\n" name
        | Some why -> fail_with why
      end else begin
        let bind_all vs = List.iter2 (fun (v : Types.var) x -> Interp.bind env v x) inputs vs in
        let valid vs =
          bind_all vs;
          match cond with
          | None -> true
          | Some c -> (match Interp.eval env c with Interp.VBool b -> b | _ -> false | exception _ -> false) in
        (* what a failing case printed is dropped: only the smallest case is reported *)
        let run vs =
          bind_all vs;
          let before = Buffer.length Interp.out in
          let r = attempt () in
          if r <> None then Buffer.truncate Interp.out before;
          r in
        let s = Proptest.seed_of name seed in
        match Proptest.check env ~cases ~seed:s inputs ~valid ~run with
        | Proptest.Passed n -> incr pass; Interp.flush_out (); Printf.printf "ok   %s (%d cases)\n" name n
        | Proptest.Too_few (ok, made) -> fail_with (Printf.sprintf "too few valid inputs: the where clause passed %d of %d" ok made)
        | Proptest.Cannot t -> fail_with (Printf.sprintf "no inputs can be generated for the type %s" (Types.show_ty t))
        | Proptest.Failed_case (why, shown, s) ->
            fail_with (Printf.sprintf "%s\n     smallest failing input: %s\n     seed %d (--seed %d runs it again)" why (String.concat ", " shown) s s)
      end)
    prog.tests;
  (* rejection tests: the body must fail to compile with the given code *)
  List.iter
    (fun (t : Syntax.test_def) ->
      let code = Option.get t.tsrejects in
      let others = List.filter (function ITest _ -> false | _ -> true) user.items in
      let probe = { user with items = others @ [ ITest { t with tsrejects = None } ] } in
      let result = try ignore (Typecheck.check_program (load_prelude ()) imported probe); None with Error (c, _, m) -> Some (c, m) in
      match result with
      | Some (c, _) when c = code -> incr pass; Printf.printf "ok   %s (rejects %s)\n" t.tsname code
      | Some (c, m) -> incr failn; Printf.printf "FAIL %s: expected %s, got %s: %s\n" t.tsname code c m
      | None -> incr failn; Printf.printf "FAIL %s: expected %s, but it compiled\n" t.tsname code)
    (Typecheck.rejection_tests user);
  Printf.printf "\n%d passed, %d failed\n" !pass !failn;
  !failn > 0

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let interp = ref false and release = ref false and out = ref None and cc = ref None and keep = ref false and explain = ref None and profile = ref false in
  let update = ref false and cases = ref 100 and seed = ref None in
  let rec parse_opts acc = function
    | "--interp" :: rest -> interp := true; parse_opts acc rest
    | "--release" :: rest -> release := true; parse_opts acc rest
    | "--json" :: rest -> json := true; parse_opts acc rest
    | "--keep-c" :: rest -> keep := true; parse_opts acc rest
    | "--explain-copies" :: rest -> explain := Some (ref []); parse_opts acc rest
    | "--profile-copies" :: rest -> profile := true; parse_opts acc rest
    | "--update-snapshots" :: rest -> update := true; parse_opts acc rest
    | "--cases" :: n :: rest when int_of_string_opt n <> None ->
        (* a run of no cases would pass whatever the property says *)
        if int_of_string n <= 0 || int_of_string n > 1_000_000 then (prerr_endline "error: --cases takes a number from 1 to 1000000"; exit 2);
        cases := int_of_string n; parse_opts acc rest
    | "--seed" :: n :: rest when int_of_string_opt n <> None -> seed := int_of_string_opt n; parse_opts acc rest
    | "-o" :: p :: rest -> out := Some p; parse_opts acc rest
    | "--cc" :: p :: rest -> cc := Some p; parse_opts acc rest
    | x :: rest -> parse_opts (x :: acc) rest
    | [] -> List.rev acc
  in
  let pos = parse_opts [] args in
  let cmd, file =
    match pos with
    | [ c; f ] -> (c, f)
    | _ -> print_string usage; exit (if pos = [] then 0 else 2)
  in
  try
    let user, imported, prog = front_end ~docs:(cmd = "test") ~bench:(cmd = "bench") file in
    (match cmd with "check" | "test" -> Cgen.check ?explain:!explain prog | "run" when !interp -> Cgen.check ?explain:!explain prog | _ -> ());
    (* the list of --explain-copies, once the code that it describes has been generated *)
    let explained () =
      Option.iter (fun found ->
          if !found = [] then prerr_endline "no copies to explain"
          else List.iter (fun ((l : Syntax.loc), msg) -> Printf.eprintf "%s:%d:%d: %s\n" l.file l.line l.col msg) !found;
          found := []) !explain in
    explained ();
    match cmd with
    | "check" -> ()
    | "run" when !interp -> run_interp prog
    | "test" ->
        let failed = run_tests_interp ~cases:!cases ~seed:!seed ~update:!update file user imported prog in
        (* each measure block once, in the counting build, with its budgets (section 20.3) *)
        let _, _, calls = bench_blocks file (read_file file) in
        let bench_failed =
          if calls = [] then false
          else begin
            let _, _, bprog = front_end ~bench:true file in
            print_newline ();
            flush stdout;
            Backend.run { Backend.release = true; cc = !cc; keep_c = false; profile = false; explain = None; counters = true } bprog file <> 0
          end in
        if failed || bench_failed then exit 1
    | "bench" ->
        (* the counters and the times come from two builds, so that counting slows no timing *)
        let opts = { Backend.release = true; cc = !cc; keep_c = false; profile = false; explain = None; counters = true } in
        flush stdout;
        let counted = Backend.run opts prog file in
        print_newline ();
        flush stdout;
        let timed = Backend.run { opts with counters = false } prog file in
        exit (if counted <> 0 then counted else timed)
    | "run" | "build" | "emit-c" ->
        let opts = { Backend.release = !release; cc = !cc; keep_c = !keep; profile = !profile; explain = !explain; counters = false } in
        (match cmd with
         | "emit-c" -> print_string (Cgen.emit ?explain:!explain ~profile:!profile prog ~debug:(not !release)); explained ()
         | "build" ->
             let exe =
               match !out with
               | Some o -> o
               | None ->
                   (* never the source itself, which a file without an extension would be *)
                   let base = Filename.remove_extension file in
                   if base = file then file ^ ".out" else base
             in
             (* compare the files themselves, so ./x.stn or a link to the source is caught too *)
             let same_file out =
               out = file
               ||
               try
                 let a = Unix.stat file and b = Unix.stat out in
                 a.Unix.st_dev = b.Unix.st_dev && a.Unix.st_ino = b.Unix.st_ino
               with Unix.Unix_error _ -> false
             in
             (* every file the build writes: the executable, and the C file with --keep-c *)
             let outputs = exe :: (if !keep then [ exe ^ ".c" ] else []) in
             (match List.find_opt same_file outputs with
              | Some out ->
                  Printf.eprintf "error: %s is the source file; choose another output with -o\n" out;
                  exit 1
              | None -> ());
             Backend.build opts prog exe; explained ()
         | _ ->
             (* a run prints the list before the program's own output *)
             if !explain <> None then begin
               Cgen.check ?explain:!explain prog; explained ();
               exit (Backend.run { opts with explain = None } prog file)
             end else exit (Backend.run opts prog file))
    | c -> Printf.eprintf "unknown command '%s'\n%s" c usage; exit 2
  with
  | Error (code, l, msg) -> report code l msg; exit 1
  | Unsupported (msg, l) -> report "" l ("not supported yet: " ^ msg); exit 1
  | Sys_error m -> Printf.eprintf "error: %s\n" m; exit 1
  | Stack_overflow ->
      (* a program nested deeper than the compiler's own recursion can follow *)
      report "E0100" { file; line = 0; col = 0 } "the program is nested too deeply to be compiled";
      exit 1
