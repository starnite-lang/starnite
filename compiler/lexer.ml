(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Pass 1a: tokens and indentation (section 2.1). *)

open Syntax

type tok =
  | IDENT of string
  | KW of string
  | INT of string
  | FLOAT of float
  | STR of string
  | FSTR of fraw list
  | CHAR of int
  | DUR of int64 * string
  | OP of string
  | NEWLINE
  | INDENT
  | DEDENT
  | EOF

and fraw = RLit of string | RExpr of string * loc

type token = { t : tok; tloc : loc }

let keywords =
  [ "and"; "as"; "break"; "check"; "continue"; "effect"; "elif"; "else"; "ensures";
    "extern"; "false"; "fn"; "for"; "frozen"; "handle"; "if"; "impl"; "import"; "in";
    "iso"; "let"; "level"; "local"; "match"; "mut"; "not"; "or"; "par"; "resource";
    "resume"; "return"; "shared"; "spawn"; "struct"; "take"; "trait"; "true"; "try";
    "type"; "unique"; "var"; "where"; "while"; "with" ]

let is_kw s = List.mem s keywords

let show_tok = function
  | IDENT s -> Printf.sprintf "'%s'" s
  | KW s -> Printf.sprintf "'%s'" s
  | INT s -> s
  | FLOAT f -> string_of_float f
  | STR s -> Printf.sprintf "%S" s
  | FSTR _ -> "f-string"
  | CHAR _ -> "character literal"
  | DUR (n, u) -> Int64.to_string n ^ u
  | OP s -> Printf.sprintf "'%s'" s
  | NEWLINE -> "end of line"
  | INDENT -> "indentation"
  | DEDENT -> "end of block"
  | EOF -> "end of file"

(* Operators, longest first. *)
let ops3 = []
let ops2 =
  [ "->"; ".."; "=="; "!="; "<="; ">="; "+%"; "-%"; "*%"; "+="; "-="; "*="; "/="; "%=" ]
let ops1 = [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "="; "("; ")"; "["; "]"; "{"; "}"; ",";
             ":"; "."; "|"; "&"; "!"; "?"; "@" ]

let continuation_ops =
  [ "+"; "-"; "*"; "/"; "%"; "+%"; "-%"; "*%"; "=="; "!="; "<"; "<="; ">"; ">="; "&"; "|" ]

let dur_units = [ "ns"; "us"; "ms"; "s"; "min"; "h"; "b"; "kib"; "mib"; "gib" ]

(* A raw token remembers whether it starts a physical line. *)
type raw = { r : tok; rloc : loc; bol : bool }

let utf8_encode buf c =
  if c < 0x80 then Buffer.add_char buf (Char.chr c)
  else if c < 0x800 then begin
    Buffer.add_char buf (Char.chr (0xC0 lor (c lsr 6)));
    Buffer.add_char buf (Char.chr (0x80 lor (c land 0x3F)))
  end else if c < 0x10000 then begin
    Buffer.add_char buf (Char.chr (0xE0 lor (c lsr 12)));
    Buffer.add_char buf (Char.chr (0x80 lor ((c lsr 6) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor (c land 0x3F)))
  end else begin
    Buffer.add_char buf (Char.chr (0xF0 lor (c lsr 18)));
    Buffer.add_char buf (Char.chr (0x80 lor ((c lsr 12) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor ((c lsr 6) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor (c land 0x3F)))
  end

(* Decode one UTF-8 scalar at position i; returns (code, length). *)
let utf8_decode s i =
  let c = Char.code s.[i] in
  let n = String.length s in
  let cont k = if i + k < n then Char.code s.[i + k] land 0x3F else 0 in
  if c < 0x80 then (c, 1)
  else if c land 0xE0 = 0xC0 then (((c land 0x1F) lsl 6) lor cont 1, 2)
  else if c land 0xF0 = 0xE0 then (((c land 0x0F) lsl 12) lor (cont 1 lsl 6) lor cont 2, 3)
  else (((c land 0x07) lsl 18) lor (cont 1 lsl 12) lor (cont 2 lsl 6) lor cont 3, 4)

let raw_lex (file : string) (src : string) ?(line0 = 1) ?(col0 = 1) () : raw list =
  let n = String.length src in
  let toks = ref [] in
  let i = ref 0 and line = ref line0 and lstart = ref 0 in
  let col0_first = ref (col0 - 1) in
  let at_bol = ref true in
  let loc_at p = { file; line = !line; col = p - !lstart + 1 + (if !line = line0 then !col0_first else 0) } in
  let push t l =
    toks := { r = t; rloc = l; bol = !at_bol } :: !toks;
    at_bol := false
  in
  let peek k = if !i + k < n then src.[!i + k] else '\000' in
  let is_digit c = c >= '0' && c <= '9' in
  let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' in
  let is_alnum c = is_alpha c || is_digit c in
  let newline () = incr line; lstart := !i; at_bol := true in
  (* Read an escape after a backslash; returns code point. *)
  let read_escape l =
    let c = peek 0 in
    incr i;
    match c with
    | 'n' -> 10 | 't' -> 9 | 'r' -> 13 | '0' -> 0 | '\\' -> 92 | '"' -> 34 | '\'' -> 39
    | '{' -> 123 | '}' -> 125
    | 'u' ->
        if peek 0 <> '{' then error "E0100" l "malformed \\u escape";
        incr i;
        let st = !i in
        while !i < n && peek 0 <> '}' do incr i done;
        let hex = String.sub src st (!i - st) in
        incr i;
        let cp =
          match (if hex = "" || String.length hex > 6 then None else int_of_string_opt ("0x" ^ hex)) with
          | Some cp -> cp
          | None -> error "E0100" l "malformed \\u escape"
        in
        (* a Str is valid UTF-8 and a Char a Unicode scalar value (section 3.1) *)
        if cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF) then
          error "E0100" l "\\u{%s} is not a Unicode scalar value" hex;
        cp
    | _ -> error "E0100" l "unknown escape \\%c" c
  in
  while !i < n do
    let c = src.[!i] in
    if !at_bol then begin
      (* measure indentation; skip blank and comment lines *)
      while !i < n && (src.[!i] = ' ' || src.[!i] = '\t') do
        if src.[!i] = '\t' then error "E0106" (loc_at !i) "tab in indentation";
        incr i
      done;
      if !i >= n then ()
      else if src.[!i] = '\n' then (incr i; newline ())
      else if src.[!i] = '\r' then incr i
      else if src.[!i] = '#' then begin
        while !i < n && src.[!i] <> '\n' do incr i done
      end else begin
        (* line-start marker, turned into layout tokens by [layout] *)
        toks := { r = NEWLINE; rloc = loc_at !i; bol = true } :: !toks;
        at_bol := false
      end
    end else if c = ' ' || c = '\r' || c = '\t' then incr i
    else if c = '\n' then (incr i; newline ())
    else if c = '#' then begin
      while !i < n && src.[!i] <> '\n' do incr i done
    end
    else if is_digit c then begin
      let l = loc_at !i in
      let st = !i in
      if c = '0' && (peek 1 = 'x' || peek 1 = 'X') then begin
        i := !i + 2;
        while !i < n && (is_alnum src.[!i]) do incr i done;
        let s = String.sub src st (!i - st) in
        let s = String.concat "" (String.split_on_char '_' s) in
        push (INT s) l
      end else if c = '0' && peek 1 = 'b' && (peek 2 = '0' || peek 2 = '1') then begin
        i := !i + 2;
        while !i < n && (src.[!i] = '0' || src.[!i] = '1' || src.[!i] = '_') do incr i done;
        let s = String.sub src st (!i - st) in
        let s = String.concat "" (String.split_on_char '_' s) in
        push (INT s) l
      end else begin
        while !i < n && (is_digit src.[!i] || src.[!i] = '_') do incr i done;
        let is_float = ref false in
        if peek 0 = '.' && is_digit (peek 1) then begin
          is_float := true;
          incr i;
          while !i < n && (is_digit src.[!i] || src.[!i] = '_') do incr i done
        end;
        if (peek 0 = 'e' || peek 0 = 'E')
           && (is_digit (peek 1) || ((peek 1 = '-' || peek 1 = '+') && is_digit (peek 2))) then begin
          is_float := true;
          i := !i + 2;
          while !i < n && is_digit src.[!i] do incr i done
        end;
        let s = String.sub src st (!i - st) in
        let s = String.concat "" (String.split_on_char '_' s) in
        if !is_float then push (FLOAT (float_of_string s)) l
        else if is_alpha (peek 0) then begin
          let us = !i in
          while !i < n && is_alnum src.[!i] do incr i done;
          let u = String.sub src us (!i - us) in
          if List.mem u dur_units then
            match Int64.of_string_opt s with
            | Some v when Int64.compare v 0L >= 0 -> push (DUR (v, u)) l
            | _ -> error "E0201" l "literal %s%s is too large" s u
          else error "E0100" l "unknown unit '%s' after number" u
        end else push (INT s) l
      end
    end
    else if c = 'f' && peek 1 = '"' then begin
      let l = loc_at !i in
      i := !i + 2;
      let parts = ref [] in
      let buf = Buffer.create 16 in
      let flush () =
        if Buffer.length buf > 0 then (parts := RLit (Buffer.contents buf) :: !parts; Buffer.clear buf)
      in
      while !i < n && src.[!i] <> '"' do
        let ch = src.[!i] in
        if ch = '\n' then error "E0100" l "unterminated string";
        if ch = '\\' then (incr i; utf8_encode buf (read_escape l))
        else if ch = '{' then begin
          flush ();
          incr i;
          let el = loc_at !i in
          let st = !i in
          let depth = ref 0 in
          while !i < n && not (src.[!i] = '}' && !depth = 0) do
            if src.[!i] = '{' then incr depth;
            if src.[!i] = '}' then decr depth;
            if src.[!i] = '\n' then error "E0100" l "unterminated interpolation";
            incr i
          done;
          parts := RExpr (String.sub src st (!i - st), el) :: !parts;
          incr i
        end else (Buffer.add_char buf ch; incr i)
      done;
      if !i >= n then error "E0100" l "unterminated string";
      incr i;
      flush ();
      push (FSTR (List.rev !parts)) l
    end
    else if is_alpha c then begin
      let l = loc_at !i in
      let st = !i in
      while !i < n && is_alnum src.[!i] do incr i done;
      let s = String.sub src st (!i - st) in
      push (if is_kw s then KW s else IDENT s) l
    end
    else if c = '"' then begin
      let l = loc_at !i in
      incr i;
      let buf = Buffer.create 16 in
      while !i < n && src.[!i] <> '"' do
        let ch = src.[!i] in
        if ch = '\n' then error "E0100" l "unterminated string";
        if ch = '\\' then (incr i; utf8_encode buf (read_escape l))
        else (Buffer.add_char buf ch; incr i)
      done;
      if !i >= n then error "E0100" l "unterminated string";
      incr i;
      push (STR (Buffer.contents buf)) l
    end
    else if c = '\'' then begin
      let l = loc_at !i in
      incr i;
      let code =
        if peek 0 = '\\' then (incr i; read_escape l)
        else begin
          let (cp, len) = utf8_decode src !i in
          i := !i + len; cp
        end
      in
      if peek 0 <> '\'' then error "E0100" l "malformed character literal";
      incr i;
      push (CHAR code) l
    end
    else begin
      let l = loc_at !i in
      let try_ops len ops =
        if !i + len <= n then
          let s = String.sub src !i len in
          if List.mem s ops then (i := !i + len; push (OP s) l; true) else false
        else false
      in
      if not (try_ops 3 ops3 || try_ops 2 ops2 || try_ops 1 ops1) then
        error "E0100" l "unexpected character '%c'" c
    end
  done;
  List.rev !toks

(* Turn the raw stream into one with NEWLINE / INDENT / DEDENT (section 2.1).
   A NEWLINE raw token with bol=true is a line-start marker inserted by raw_lex. *)
(* Does the physical line starting with these tokens contain '->' at bracket depth 0? *)
let arm_follows (toks : raw list) =
  let rec go depth = function
    | [] -> false
    | { r = NEWLINE; bol = true; _ } :: _ -> false
    | { r = OP ("(" | "[" | "{"); _ } :: rest -> go (depth + 1) rest
    | { r = OP (")" | "]" | "}"); _ } :: rest -> go (depth - 1) rest
    | { r = OP "->"; _ } :: _ when depth = 0 -> true
    | _ :: rest -> go depth rest
  in
  go 0 toks

let layout (file : string) (raws : raw list) : token array =
  let out = ref [] in
  let emit t l = out := { t; tloc = l } :: !out in
  let stack = ref [ 0 ] in
  let depth = ref 0 in
  let last_real = ref false in
  let rec go = function
    | [] -> ()
    | { r = NEWLINE; rloc; bol = true } :: rest ->
        (* the next token starts a physical line *)
        (match rest with
         | [] -> go rest
         | nxt :: _ ->
             let cont =
               match nxt.r with
               | OP "-" ->
                   (* a match arm with a negative pattern, "-1 -> ...", starts a line;
                      any other line starting with '-' continues the previous one *)
                   not (arm_follows rest)
               | OP o -> List.mem o continuation_ops
               | KW ("and" | "or") -> true
               | _ -> false
             in
             if !depth > 0 || cont then go rest
             else begin
               if !last_real then emit NEWLINE rloc;
               last_real := false;
               let ind = rloc.col - 1 in
               let top = List.hd !stack in
               if ind > top then (stack := ind :: !stack; emit INDENT rloc)
               else if ind < top then begin
                 while ind < List.hd !stack do
                   stack := List.tl !stack;
                   emit DEDENT rloc
                 done;
                 if ind <> List.hd !stack then error "E0100" rloc "inconsistent indentation"
               end;
               go rest
             end)
    | r :: rest ->
        (match r.r with
         | OP ("(" | "[" | "{") -> incr depth
         | OP (")" | "]" | "}") -> if !depth > 0 then decr depth
         | _ -> ());
        emit r.r r.rloc;
        last_real := true;
        go rest
  in
  go raws;
  let endloc = { file; line = max_int; col = 1 } in
  if !last_real then emit NEWLINE endloc;
  List.iter (fun _ -> ()) [];
  while List.length !stack > 1 do
    stack := List.tl !stack;
    emit DEDENT endloc
  done;
  emit EOF endloc;
  Array.of_list (List.rev !out)

let tokenize file src = layout file (raw_lex file src ())

(* Tokens for an expression embedded in an f-string: no layout. *)
let tokenize_fragment (l : loc) src =
  let raws = raw_lex l.file src ~line0:l.line ~col0:l.col () in
  let toks = List.filter_map (fun r -> match r.r with NEWLINE when r.bol -> None | t -> Some { t; tloc = r.rloc }) raws in
  Array.of_list (toks @ [ { t = EOF; tloc = l } ])
