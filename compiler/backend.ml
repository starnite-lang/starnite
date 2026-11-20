(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Driving the C compiler (section 11.6). *)

type opts = { release : bool; cc : string option; keep_c : bool }

let scratch_dir () =
  let d = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "starnite-%d" (Unix.getpid ())) in
  (try Unix.mkdir d 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  d

let write path s = Out_channel.with_open_bin path (fun oc -> output_string oc s)

let cc_cmd o =
  match o.cc with
  | Some c -> c
  | None -> (match Sys.getenv_opt "CC" with Some c when c <> "" -> c | _ -> "cc")

let build o (prog : Types.tprog) (exe : string) =
  let c = Cgen.emit prog ~debug:(not o.release) in
  let dir = scratch_dir () in
  write (Filename.concat dir "stn_runtime.h") Runtime_src.header;
  write (Filename.concat dir "stn_runtime.c") Runtime_src.source;
  let cfile = if o.keep_c then exe ^ ".c" else Filename.concat dir "main.c" in
  write cfile c;
  let flags = if o.release then "-O2 -fno-strict-aliasing" else "-O0 -g -DSTN_DEBUG" in
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
