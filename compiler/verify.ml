(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Checks of `noalloc fn` and `inplace fn` (section 9.6).

   The spec states both checks on Counted Core, the form of a function after count updates, reuse
   and destination passing. This compiler has no such form of its own: those decisions are taken
   while C is written, so the C is where they can be seen, and it is what is checked. A function
   body is read as a list of the names it calls or mentions, and every name is one of:
   - a function of the generated program, whose own body is read the same way;
   - a function or macro of the runtime from which no path reaches the allocator ([quiet]);
   - anything else, which is taken to allocate.
   A name that is missing from the lists is therefore an error reported where there is none, never
   an allocation that goes unseen. A call through a pointer (a closure, a method of an `any`
   value) can reach any function and counts as allocating. Mentioning a function without calling
   it, as when a table of element operations is handed to the runtime, counts as calling it. *)

open Syntax

type fn_record = {
  cname : string;                        (* its name in C *)
  display : string;                      (* its name in the program *)
  mods : string list;
  floc : loc;
  text : string;                         (* the whole definition *)
  marks : (int * loc * string * bool) list;   (* where the code of each expression starts, ascending, and whether a loop of the program is around it *)
  excused : (int * int) list;            (* the paths taken when a `take` argument is shared *)
  stray : loc option;                    (* a call of itself that is not a tail or constructor-tail call *)
}

(* the checked arithmetic of the runtime, which one macro defines for every operation and width,
   and what the C compiler itself provides *)
let arithmetic =
  List.concat_map (fun op -> List.map (fun w -> Printf.sprintf "stn_%s_%s" op w) [ "i64"; "i32"; "i16"; "i8"; "u64"; "u32"; "u16"; "u8" ])
    [ "add"; "sub"; "mul"; "div"; "rem" ]
let quiet_prefixes = [ "__builtin_"; "_mm" ]
(* a trap that builds its message first: the program ends there, so what it allocates is moot *)
let final = [ "stn_trap_str" ]

(* C itself, and the functions of its library that the generated code uses *)
let c_names = [
  "if"; "for"; "while"; "switch"; "return"; "sizeof"; "do"; "else"; "case"; "goto"; "break"; "continue"; "default";
  "INT64_C"; "UINT64_C"; "INT32_C"; "UINT32_C"; "memcpy"; "memcmp"; "memmove"; "memset"; "offsetof";
  "fmod"; "fmodf"; "sqrt"; "sqrtf"; "floor"; "floorf"; "ceil"; "ceilf"; "fabs"; "fabsf"; "trunc"; "truncf";
  "round"; "roundf"; "pow"; "powf"; "exp"; "log"; "sin"; "cos"; "tan"; "isnan"; "isinf"; "isfinite";
]

(* names whose call is a count increment, which an inplace function must not make *)
let dups = [ "stn_dup"; "stn_str_dup"; "STN_STR_DUP"; "stn_error_dup" ]

(* why a name of the runtime can allocate, for the names a program most often meets *)
let reason name =
  match name with
  | "stn_alloc" -> "it allocates a cell"
  | "stn_array_make_unique" | "stn_array_copy_for_write" | "STN_POP" | "stn_array_clear" | "stn_array_remove"
  | "stn_array_reverse_i64" | "stn_array_sort_i64" ->
      "it writes to an array, which is copied first if anything else holds it"
  | "stn_map_make_unique_for_write" | "stn_map_remove" | "stn_map_clear" ->
      "it writes to a map or set, which is copied first if anything else holds it"
  | "STN_PUSH" | "STN_PUSH_UNIQUE" | "stn_array_push" | "stn_array_extend" | "stn_array_insert" | "stn_array_reserve"
  | "stn_array_reserve_hint" -> "it can grow an array"
  | "stn_map_put" | "stn_map_slot_ref" | "stn_map_slot" -> "it can grow a map or set"
  | "stn_array_new" | "stn_array_filled" | "stn_array_filled_i64" | "stn_array_slice" -> "it builds an array"
  | "stn_map_new" | "stn_map_with_capacity" | "stn_set_union" | "stn_set_intersection" | "stn_set_difference" ->
      "it builds a map or set"
  | "stn_str_dup" | "STN_STR_DUP" -> "it keeps a string, which is copied if it is a view of another"
  | "stn_str_new" | "stn_str_concat" | "stn_str_concat_n" | "stn_str_append" | "stn_str_join" | "stn_str_join_parts"
  | "stn_str_repeat" | "stn_str_slice" | "stn_str_slice_self" | "stn_str_trim" -> "it can build a string longer than fits inline"
  | "stn_str_split" | "stn_str_chars" -> "it builds an array of strings"
  | "stn_read_line" | "stn_read_all" -> "it reads into a new string"
  | "stn_parse_float" -> "it copies a long number before reading it"
  | "(pointer)" -> "it calls through a closure or an `any` value, which can reach any function"
  | n when String.length n > 9 && String.sub n 0 9 = "stn_show_" -> "it builds a string"
  | n when String.length n > 8 && String.sub n 0 8 = "errmake_" -> "it builds an error value"
  | n -> Printf.sprintf "it uses %s, which is not known to be free of allocation" n

let is_ident_start c = c = '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let is_ident c = is_ident_start c || (c >= '0' && c <= '9')

type token = Call of string | Ref of string | Pointer

(* The names in text.[lo, hi), each with its offset: [Call] when an argument list follows, [Pointer]
   for a call through a member of a structure, [Ref] for any other mention. Strings, characters
   and comments are skipped. *)
let tokens (text : string) lo hi (f : int -> token -> unit) =
  let i = ref lo in
  let skip_space j = let j = ref j in while !j < hi && (text.[!j] = ' ' || text.[!j] = '\n' || text.[!j] = '\t') do incr j done; !j in
  while !i < hi do
    let c = text.[!i] in
    if c = '"' || c = '\'' then begin
      incr i;
      while !i < hi && text.[!i] <> c do (if text.[!i] = '\\' then incr i); incr i done;
      incr i
    end else if c = '/' && !i + 1 < hi && text.[!i + 1] = '*' then begin
      i := !i + 2;
      while !i + 1 < hi && not (text.[!i] = '*' && text.[!i + 1] = '/') do incr i done;
      i := !i + 2
    end else if is_ident_start c then begin
      let s = !i in
      while !i < hi && is_ident text.[!i] do incr i done;
      let name = String.sub text s (!i - s) in
      let member = (s >= 2 && text.[s - 2] = '-' && text.[s - 1] = '>') || (s >= 1 && text.[s - 1] = '.') in
      let j = skip_space !i in
      (* a type before a parenthesized star is the type of a function pointer, not a call *)
      let called = j < hi && text.[j] = '(' && not (j + 2 < hi && text.[j + 1] = '*' && text.[j + 2] = ')') in
      (* a member that is called, with or without a cast closed around it *)
      let cast_called = j < hi && text.[j] = ')' && (let k = skip_space (j + 1) in k < hi && text.[k] = '(') in
      if member then (if called || cast_called then f s Pointer)
      else f s (if called then Call name else Ref name)
    end else if c >= '0' && c <= '9' then begin
      (* a number, with any suffix: not a name *)
      while !i < hi && (is_ident text.[!i] || text.[!i] = '.') do incr i done
    end else incr i
  done

(* The definitions at the top level of generated C: functions, and tables of functions, each with
   the bounds of its body. *)
let definitions (text : string) : (string * int * int) list =
  let n = String.length text in
  let out = ref [] in
  let depth = ref 0 and paren = ref 0 and last_call = ref None and last_ref = ref None and start = ref 0 and name = ref None in
  let i = ref 0 in
  while !i < n do
    let c = text.[!i] in
    if c = '"' || c = '\'' then begin
      incr i;
      while !i < n && text.[!i] <> c do (if text.[!i] = '\\' then incr i); incr i done;
      incr i
    end else if c = '/' && !i + 1 < n && text.[!i + 1] = '*' then begin
      i := !i + 2;
      while !i + 1 < n && not (text.[!i] = '*' && text.[!i + 1] = '/') do incr i done;
      i := !i + 2
    end else if c = '{' then begin
      if !depth = 0 then begin
        (* a function is named by the last name before an argument list; a table by the last name *)
        name := (match !last_call with Some _ as x -> x | None -> !last_ref);
        start := !i + 1
      end;
      incr depth; incr i
    end else if c = '}' then begin
      decr depth;
      if !depth = 0 then begin
        (match !name with Some nm -> out := (nm, !start, !i) :: !out | None -> ());
        last_call := None; last_ref := None
      end;
      incr i
    end else if c = '(' then (incr paren; incr i)
    else if c = ')' then (decr paren; incr i)
    else if c = ';' && !depth = 0 then (last_call := None; last_ref := None; incr i)
    else if is_ident_start c then begin
      let s = !i in
      while !i < n && is_ident text.[!i] do incr i done;
      if !depth = 0 && !paren = 0 then begin
        let nm = String.sub text s (!i - s) in
        let j = ref !i in
        while !j < n && text.[!j] = ' ' do incr j done;
        if !j < n && text.[!j] = '(' then (if nm <> "__attribute__" then last_call := Some nm) else last_ref := Some nm
      end
    end else incr i
  done;
  List.rev !out

let starts_with p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p

(* What the runtime does without allocating: its functions, and its macros that take arguments,
   from which no path reaches the allocator of C. Read from the runtime's own source, which the
   compiler carries, so the list cannot fall behind it. *)
(* the functions of the runtime, by name: not its macros *)
let runtime_functions : string list ref = ref []

let quiet : (string, unit) Hashtbl.t Lazy.t = lazy (
  let src = Runtime_src.header ^ "\n" ^ Runtime_src.source in
  (* a line that ends in a backslash goes on *)
  let src =
    let b = Buffer.create (String.length src) and n = String.length src and i = ref 0 in
    while !i < n do
      if src.[!i] = '\\' && !i + 1 < n && src.[!i + 1] = '\n' then (Buffer.add_string b "  "; i := !i + 2)
      else (Buffer.add_char b src.[!i]; incr i)
    done;
    Buffer.contents b in
  let bodies : (string, string) Hashtbl.t = Hashtbl.create 256 in
  let add name body = Hashtbl.replace bodies name ((try Hashtbl.find bodies name with Not_found -> "") ^ "\n" ^ body) in
  (* directives are taken out; a macro with arguments is kept as a function with its text as body *)
  let plain = Buffer.create (String.length src) in
  List.iter (fun l ->
      let t = String.trim l in
      if t <> "" && t.[0] = '#' then begin
        let t = String.trim (String.sub t 1 (String.length t - 1)) in
        (if starts_with "define" t then
           let t = String.trim (String.sub t 6 (String.length t - 6)) in
           let k = ref 0 in
           while !k < String.length t && is_ident t.[!k] do incr k done;
           if !k < String.length t && t.[!k] = '(' then
             match String.index_from_opt t !k ')' with
             | Some close -> add (String.sub t 0 !k) (String.sub t (close + 1) (String.length t - close - 1))
             | None -> ());
        Buffer.add_char plain '\n'
      end else (Buffer.add_string plain l; Buffer.add_char plain '\n')) (String.split_on_char '\n' src);
  let plain = Buffer.contents plain in
  List.iter (fun (nm, lo, hi) -> add nm (String.sub plain lo (hi - lo)); runtime_functions := nm :: !runtime_functions) (definitions plain);
  let calls = Hashtbl.create 256 in
  Hashtbl.iter (fun nm body ->
      let acc = ref [] in
      tokens body 0 (String.length body) (fun _ tok -> match tok with Call n -> acc := n :: !acc | _ -> ());
      Hashtbl.replace calls nm !acc) bodies;
  let alloc = Hashtbl.create 64 in
  List.iter (fun n -> Hashtbl.replace alloc n ()) [ "malloc"; "calloc"; "realloc"; "aligned_alloc"; "posix_memalign"; "strdup"; "getline"; "fopen" ];
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter (fun nm cs ->
        if not (Hashtbl.mem alloc nm) && List.exists (Hashtbl.mem alloc) cs then (Hashtbl.replace alloc nm (); changed := true)) calls
  done;
  let q = Hashtbl.create 256 in
  Hashtbl.iter (fun nm _ -> if not (Hashtbl.mem alloc nm) then Hashtbl.replace q nm ()) bodies;
  q)

type cause = Direct of int * string | Via of int * string   (* offset in the body; the runtime name, or the function called *)

let run ~(records : fn_record list) ~(names : (string * string) list) ~(text : string) : unit =
  let quiet_set = Hashtbl.create 128 in
  List.iter (fun n -> Hashtbl.replace quiet_set n ()) (c_names @ arithmetic @ final);
  let is_quiet n = Hashtbl.mem quiet_set n || Hashtbl.mem (Lazy.force quiet) n || List.exists (fun p -> starts_with p n) quiet_prefixes in
  let dup_set = Hashtbl.create 8 in
  List.iter (fun n -> Hashtbl.replace dup_set n ()) dups;
  (* every definition: name -> its text and the bounds of its body *)
  let defs : (string, string * int * int) Hashtbl.t = Hashtbl.create 256 in
  List.iter (fun (nm, lo, hi) -> Hashtbl.replace defs nm (text, lo, hi)) (definitions text);
  let by_cname = Hashtbl.create 64 in
  List.iter (fun r ->
      Hashtbl.replace by_cname r.cname r;
      match definitions r.text with
      | (_, lo, hi) :: _ -> Hashtbl.replace defs r.cname (r.text, lo, hi)
      | [] -> ()) records;
  let is_inplace n = match Hashtbl.find_opt by_cname n with Some r -> List.mem "inplace" r.mods | None -> false in
  (* names in a body that are not variables of its own: those followed by an argument list, and
     those that are definitions *)
  let uses name : (int * token) list =
    match Hashtbl.find_opt defs name with
    | None -> []
    | Some (t, lo, hi) ->
        let acc = ref [] in
        tokens t lo hi (fun off tok ->
            match tok with
            | Ref n -> if Hashtbl.mem defs n && n <> name then acc := (off, tok) :: !acc
            | Call _ | Pointer -> acc := (off, tok) :: !acc);
        List.rev !acc
  in
  let all_uses = Hashtbl.create 256 in
  Hashtbl.iter (fun name _ -> Hashtbl.replace all_uses name (uses name)) defs;
  (* the first cause of allocation in each function, to a fixed point *)
  let alloc : (string, cause) Hashtbl.t = Hashtbl.create 64 in
  let dupping : (string, unit) Hashtbl.t = Hashtbl.create 64 in
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter (fun name us ->
        if not (Hashtbl.mem alloc name) then begin
          let cause = List.find_map (fun (off, tok) ->
              match tok with
              | Pointer -> Some (Direct (off, "(pointer)"))
              | Call n | Ref n ->
                  if n = name then None
                  else if Hashtbl.mem defs n then (if Hashtbl.mem alloc n then Some (Via (off, n)) else None)
                  else if is_quiet n then None
                  else Some (Direct (off, n))) us in
          match cause with Some c -> Hashtbl.replace alloc name c; changed := true | None -> ()
        end;
        (* a helper that increments a count on behalf of whoever calls it *)
        if not (Hashtbl.mem dupping name) && not (Hashtbl.mem by_cname name) then
          if List.exists (fun (_, tok) -> match tok with
              | Call n -> Hashtbl.mem dup_set n || Hashtbl.mem dupping n
              | _ -> false) us
          then (Hashtbl.replace dupping name (); changed := true)) all_uses
  done;
  (* STN_VERIFY_NAMES=1 lists the names taken to allocate only because no list has them: the
     corpus is run this way to keep the lists whole (tests/verify_lists.sh) *)
  if Sys.getenv_opt "STN_VERIFY_NAMES" <> None then begin
    let seen = Hashtbl.create 16 in
    Hashtbl.iter (fun _ us -> List.iter (fun (_, tok) -> match tok with
        | Call n when not (Hashtbl.mem defs n) && not (is_quiet n) && starts_with "it uses" (reason n) ->
            if not (Hashtbl.mem seen n) then (Hashtbl.replace seen n (); prerr_endline ("unlisted: " ^ n))
        | _ -> ()) us) all_uses
  end;
  let shown n = match List.assoc_opt n names with Some d -> Printf.sprintf "'%s'" d | None -> n in
  let is_fn n = List.mem_assoc n names in
  (* the last cause down a chain of calls, for the message *)
  let rec root n depth = match Hashtbl.find_opt alloc n with
    | Some (Via (_, m)) when depth < 64 -> root m (depth + 1)
    | Some (Direct (_, r)) -> reason r
    | _ -> "it can allocate" in
  let mark_at (r : fn_record) off =
    List.fold_left (fun best (o, l, d, _) -> if o <= off then (l, d) else best) (r.floc, "this function") r.marks in
  let excused (r : fn_record) off = List.exists (fun (lo, hi) -> off >= lo && off < hi) r.excused in
  let errors = ref [] in
  let report code (l : loc) msg = errors := (code, l, msg) :: !errors in
  List.iter (fun (r : fn_record) ->
      if List.mem "noalloc" r.mods then begin
        match Hashtbl.find_opt alloc r.cname with
        | Some (Direct (off, n)) ->
            let l, what = mark_at r off in
            report "E0601" l (Printf.sprintf "noalloc fn '%s' can allocate at %s: %s" r.display what (reason n))
        | Some (Via (off, m)) ->
            let l, what = mark_at r off in
            report "E0601" l
              (Printf.sprintf "noalloc fn '%s' can allocate at %s: %s" r.display what
                 (if is_fn m then Printf.sprintf "%s can allocate (%s)" (shown m) (root m 0) else root m 0))
        | None -> ()
      end;
      if List.mem "inplace" r.mods then begin
        (match r.stray with
         | Some l ->
             report "E0605" l
               (Printf.sprintf "inplace fn '%s' calls itself here, directly or through another function, and the call is neither a tail call nor the one field of a constructor it returns" r.display)
         | None -> ());
        List.iter (fun (off, tok) ->
            if not (excused r off) then begin
              let l, what = mark_at r off in
              match tok with
              | Pointer ->
                  report "E0604" l (Printf.sprintf "inplace fn '%s' can allocate at %s: %s" r.display what (reason "(pointer)"))
              | Call n when Hashtbl.mem dup_set n || Hashtbl.mem dupping n ->
                  report "E0603" l
                    (Printf.sprintf "inplace fn '%s' duplicates a counted value at %s: something else goes on holding it" r.display what)
              | Call n | Ref n ->
                  if n = r.cname || is_inplace n then ()
                  else if Hashtbl.mem defs n then begin
                    if Hashtbl.mem alloc n then
                      (if is_fn n then
                         report "E0604" l
                           (Printf.sprintf "inplace fn '%s' calls %s, which is not inplace and can allocate (%s)" r.display (shown n) (root n 0))
                       else report "E0602" l (Printf.sprintf "inplace fn '%s' can allocate at %s: %s" r.display what (root n 0)))
                  end
                  else if is_quiet n then ()
                  else if n = "stn_alloc" then
                    report "E0602" l (Printf.sprintf "inplace fn '%s' allocates: no reusable cell reaches %s" r.display what)
                  else report "E0602" l (Printf.sprintf "inplace fn '%s' can allocate at %s: %s" r.display what (reason n))
            end) (try Hashtbl.find all_uses r.cname with Not_found -> [])
      end) records;
  (* the first in the order of the program *)
  match List.sort (fun (_, (a : loc), _) (_, (b : loc), _) -> compare (a.file, a.line, a.col) (b.file, b.line, b.col)) !errors with
  | (code, l, msg) :: _ -> raise (Error (code, l, msg))
  | [] -> ()

(* ---------- reporting copies (section 9.8) ---------- *)

(* the generated functions that raise a count for whoever calls them: dup_List and the like *)
let dup_helpers (helpers : string) : string list =
  let defs = Hashtbl.create 64 in
  List.iter (fun (nm, lo, hi) -> Hashtbl.replace defs nm (lo, hi)) (definitions helpers);
  let found = Hashtbl.create 16 in
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter (fun nm (lo, hi) ->
        if not (Hashtbl.mem found nm) then begin
          let hit = ref false in
          tokens helpers lo hi (fun _ tok -> match tok with
              | Call n when List.mem n dups || Hashtbl.mem found n -> hit := true
              | _ -> ());
          if !hit then (Hashtbl.replace found nm (); changed := true)
        end) defs
  done;
  List.sort compare (Hashtbl.fold (fun nm () acc -> nm :: acc) found [])

(* What --explain-copies lists: each write that copies its array, map or set first when something
   else holds it (section 4.5), and each count raised inside a loop of the program. One line per place and kind, in the order of the program. *)
let explain ~(records : fn_record list) ~(helpers : string) : (loc * string) list =
  (* the helpers alone: a function of the program that raises a count somewhere inside is not a
     count raised where it is called *)
  let helpers = dup_helpers helpers in
  let out = ref [] in
  let array_writes = [ "stn_array_make_unique"; "stn_array_copy_for_write"; "STN_POP"; "STN_PUSH"; "stn_array_push"; "stn_array_extend";
                       "stn_array_insert"; "stn_array_remove"; "stn_array_clear"; "stn_array_sort_i64"; "stn_array_reverse_i64" ] in
  let map_writes = [ "stn_map_make_unique_for_write"; "stn_map_put"; "stn_map_slot"; "stn_map_slot_ref"; "stn_map_remove"; "stn_map_clear" ] in
  List.iter (fun (r : fn_record) ->
      match definitions r.text with
      | (_, lo, hi) :: _ ->
          tokens r.text lo hi (fun off tok ->
              let l, what, in_loop =
                List.fold_left (fun best (o, l, d, lp) -> if o <= off then (l, d, lp) else best) (r.floc, "this function", false) r.marks in
              let say msg = out := (l, Printf.sprintf "in '%s', %s %s" r.display what msg) :: !out in
              match tok with
              (* an array being built is held by nothing else yet *)
              | Call n when List.mem n array_writes ->
                  if what <> "this array literal" && what <> "this comprehension" then
                    say "writes to an array, which is copied first if anything else holds it"
              (* a map or set being built by a literal is held by nothing else yet *)
              | Call n when List.mem n map_writes ->
                  if what <> "this call of lit" then say "writes to a map or set, which is copied first if anything else holds it"
              (* outside a loop a string kept is one count, like any other; --profile-copies says
                 when one was a view and had to be copied *)
              | Call ("stn_str_dup" | "STN_STR_DUP") ->
                  if in_loop then say "keeps a string in a loop: its count is raised each time, and it is copied if it is a view of another"
              | Call n when in_loop && (List.mem n dups || List.mem n helpers) -> say "raises a count in a loop"
              | _ -> ())
      | [] -> ()) records;
  List.sort_uniq (fun ((a : loc), x) ((b : loc), y) -> compare (a.file, a.line, a.col, x) (b.file, b.line, b.col, y)) !out
