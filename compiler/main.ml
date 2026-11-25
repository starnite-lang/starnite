(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* The starnite command (section 19.5). *)

open Syntax

let usage =
  {|usage: starnite <command> [options] <file.stn>

commands:
  run <file>      compile and run (add --interp to use the reference interpreter)
  build <file>    compile to an executable next to the source (or -o <path>)
  check <file>    check without generating code
  test <file>     run the test blocks of a file
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

let front_end file =
  let src = read_file file in
  let pre = load_prelude () in
  let user = Parser.parse_file file src in
  let imported = Loader.load ~entry:file user in
  (user, imported, Typecheck.check_program pre imported user)

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

(* starnite test: each test runs alone; a trap fails only that test (section 22.1). *)
let run_tests_interp file (user : Syntax.file) imported (prog : Types.tprog) =
  let pass = ref 0 and failn = ref 0 in
  List.iter
    (fun (name, body, (l : loc)) ->
      let env = { Interp.prog; vars = Hashtbl.create 16; sub = [] } in
      let fail_with msg =
        incr failn;
        Interp.flush_out ();
        Printf.printf "FAIL %s (%s:%d)\n     %s\n" name l.file l.line msg
      in
      match Interp.eval env body with
      | _ | (exception Interp.Return _) ->
          (* a return in a test block ends the test normally *)
          incr pass; Interp.flush_out (); Printf.printf "ok   %s\n" name
      | exception Interp.Failed (t, v) -> fail_with ("failed with " ^ Interp.show_value env t v)
      | exception Interp.Assert_failed (msg, al) -> fail_with (Printf.sprintf "%s at %s:%d:%d" msg al.file al.line al.col)
      | exception Values.Trap (kind, tl, msg) -> fail_with (Printf.sprintf "trap: %s at %s:%d:%d: %s" kind tl.file tl.line tl.col msg)
      | exception Stack_overflow -> fail_with "trap: stack overflow")
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
  if !failn > 0 then exit 1

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let interp = ref false and release = ref false and out = ref None and cc = ref None and keep = ref false and explain = ref None and profile = ref false in
  let rec parse_opts acc = function
    | "--interp" :: rest -> interp := true; parse_opts acc rest
    | "--release" :: rest -> release := true; parse_opts acc rest
    | "--json" :: rest -> json := true; parse_opts acc rest
    | "--keep-c" :: rest -> keep := true; parse_opts acc rest
    | "--explain-copies" :: rest -> explain := Some (ref []); parse_opts acc rest
    | "--profile-copies" :: rest -> profile := true; parse_opts acc rest
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
    let user, imported, prog = front_end file in
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
    | "test" -> run_tests_interp file user imported prog
    | "run" | "build" | "emit-c" ->
        let opts = { Backend.release = !release; cc = !cc; keep_c = !keep; profile = !profile; explain = !explain } in
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
