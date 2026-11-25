(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Driving the C compiler (section 11.6). *)

type opts = {
  release : bool; cc : string option; keep_c : bool;
  profile : bool;                                     (* --profile-copies (section 9.8) *)
  counters : bool;                                    (* the counting build of a bench (section 20.3) *)
  explain : (Syntax.loc * string) list ref option;    (* --explain-copies: where the list goes *)
}

(* A fresh private directory: the name is random, and an existing path is never reused,
   so nobody else can place or swap the files that are compiled and run. *)
let scratch_dir () =
  Random.self_init ();
  let base = Filename.get_temp_dir_name () in
  let rec attempt n =
    let d = Filename.concat base (Printf.sprintf "starnite-%d-%08x%08x" (Unix.getpid ()) (Random.bits ()) (Random.bits ())) in
    match Unix.mkdir d 0o700 with
    | () -> d
    | exception Unix.Unix_error (Unix.EEXIST, _, _) when n < 100 -> attempt (n + 1)
  in
  attempt 0

let write path s = Out_channel.with_open_bin path (fun oc -> output_string oc s)

let cc_cmd o =
  match o.cc with
  | Some c -> c
  | None -> (match Sys.getenv_opt "CC" with Some c when c <> "" -> c | _ -> "cc")

let build o (prog : Types.tprog) (exe : string) =
  let c = Cgen.emit ?explain:o.explain ~profile:o.profile prog ~debug:(not o.release) in
  let dir = scratch_dir () in
  write (Filename.concat dir "stn_runtime.h") Runtime_src.header;
  write (Filename.concat dir "stn_runtime.c") Runtime_src.source;
  let cfile = if o.keep_c then exe ^ ".c" else Filename.concat dir "main.c" in
  write cfile c;
  (* A release build starts every function and loop on a 64-byte boundary. Without it the speed of
     a loop depends on where the code before it happens to end: moving unchanged code by sixteen
     bytes changed single benchmarks by up to 80%. It costs about 5% of the size of the code. *)
  let flags = if o.release then "-O2 -fno-strict-aliasing -falign-functions=64 -falign-loops=64" else "-O0 -g -DSTN_DEBUG" in
  (* the runtime counts copies only when it is compiled to *)
  let flags = if o.profile then flags ^ " -DSTN_PROFILE_COPIES" else flags in
  let flags = if o.counters then flags ^ " -DSTN_COUNTERS" else flags in
  let cmd =
    Printf.sprintf "%s -std=c11 %s -w -I%s -o %s %s %s -lm" (cc_cmd o) flags (Filename.quote dir) (Filename.quote exe)
      (Filename.quote cfile) (Filename.quote (Filename.concat dir "stn_runtime.c"))
  in
  let status = Sys.command cmd in
  List.iter (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ()) [ "stn_runtime.h"; "stn_runtime.c"; "main.c" ];
  (try Unix.rmdir dir with _ -> ());
  if status <> 0 then begin
    Printf.eprintf "error: the C compiler failed (%s)\n" cmd;
    exit 1
  end

let run o prog file =
  let dir = scratch_dir () in
  let exe = Filename.concat dir "a.out" in
  build o prog exe;
  let status = Sys.command (Filename.quote exe) in
  (try Sys.remove exe; Unix.rmdir dir with _ -> ());
  status
