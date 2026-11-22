(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Pass 2, the loading half (section 3.5): find the modules a program imports.

   One file is one module. `import geometry.vec` loads `geometry/vec.stn`, looked up from the
   directory of the file given to the compiler, whichever module the import is in (package
   roots arrive with section 3.8). A module is loaded once, and comes after the modules it
   imports. An import cycle is an error. *)

open Syntax

let read_file f = In_channel.with_open_bin f In_channel.input_all

let canonical f = try Unix.realpath f with Unix.Unix_error _ -> f

(* The modules that [user], the module of the file [entry], imports, directly or not, as
   (path, syntax) pairs: each one after the modules it imports. *)
let load ~(entry : string) (user : Syntax.file) : (string * Syntax.file) list =
  let root = Filename.dirname entry in
  let loaded : (string, unit) Hashtbl.t = Hashtbl.create 8 in
  let order = ref [] in
  (* [stack] is the modules being loaded, the innermost first, with their files *)
  let rec visit stack (f : Syntax.file) =
    List.iter
      (function
        | IImport (p, _, l) ->
            let path = String.concat "." p in
            if path = "core" then error "E0101" l "'core' is the name of the prelude; a module of that name cannot be imported";
            let file = Filename.concat root (String.concat "/" p ^ ".stn") in
            let canon = canonical file in
            if List.exists (fun (_, c) -> c = canon) stack then begin
              let rec upto acc = function
                | [] -> acc
                | (n, c) :: rest -> if c = canon then n :: acc else upto (n :: acc) rest
              in
              let names = upto [] stack in
              error "E0101" l "import cycle: %s" (String.concat " -> " (names @ [ List.hd names ]))
            end;
            if not (Hashtbl.mem loaded path) then begin
              let src =
                try read_file file with Sys_error _ -> error "E0101" l "unknown module '%s': there is no file %s" path file
              in
              let m = Parser.parse_file file src in
              visit ((path, canon) :: stack) m;
              Hashtbl.replace loaded path ();
              order := (path, m) :: !order
            end
        | _ -> ())
      f.items
  in
  let name = Filename.remove_extension (Filename.basename entry) in
  visit [ (name, canonical entry) ] user;
  List.rev !order
