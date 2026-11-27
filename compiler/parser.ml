(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Pass 1b: recursive-descent parser for the grammar of section 2.2. *)

open Syntax
open Lexer

type st = { toks : token array; mutable pos : int; file : string }

let peek st = st.toks.(st.pos).t
let peek_at st k =
  let i = min (st.pos + k) (Array.length st.toks - 1) in
  st.toks.(i).t
let loc st = st.toks.(st.pos).tloc
let advance st = if st.pos < Array.length st.toks - 1 then st.pos <- st.pos + 1

let fail st fmt =
  Printf.ksprintf (fun m -> raise (Error ("E0100", loc st, m))) fmt

let unexpected st what =
  fail st "expected %s, found %s" what (show_tok (peek st))

let is_op st o = match peek st with OP o' when o = o' -> true | _ -> false
let is_kw st k = match peek st with KW k' when k = k' -> true | _ -> false
let is_ident st s = match peek st with IDENT s' when s = s' -> true | _ -> false

let expect_op st o = if is_op st o then advance st else unexpected st (Printf.sprintf "'%s'" o)
let expect_kw st k = if is_kw st k then advance st else unexpected st (Printf.sprintf "'%s'" k)
let accept_op st o = if is_op st o then (advance st; true) else false
let accept_kw st k = if is_kw st k then (advance st; true) else false

let expect_newline st =
  match peek st with
  | NEWLINE -> advance st
  | EOF | DEDENT -> ()
  | _ -> unexpected st "end of line"

let ident st =
  match peek st with
  | IDENT s -> advance st; s
  | _ -> unexpected st "a name"

let is_upper s = s <> "" && s.[0] >= 'A' && s.[0] <= 'Z'

(* After '.', any word is accepted as a field or method name. *)
let member_name st =
  match peek st with
  | IDENT s | KW s -> advance st; s
  | INT s -> advance st; s
  | _ -> unexpected st "a field or method name"

let comma_list st close f =
  let rec go acc =
    if is_op st close then List.rev acc
    else begin
      let x = f st in
      if accept_op st "," then go (x :: acc)
      else (if not (is_op st close) then unexpected st (Printf.sprintf "',' or '%s'" close);
            List.rev (x :: acc))
    end
  in
  go []

(* ---------- types ---------- *)

let rec parse_type st : ty =
  let l = loc st in
  let qual =
    match peek st with
    | KW ("iso" | "frozen" | "unique" as q) -> advance st; Some q
    | _ -> None
  in
  let base = parse_base_type st in
  let rec opts t = if is_op st "?" then (advance st; opts (TyOpt (t, l))) else t in
  let t = opts base in
  match qual with Some q -> TyQual (q, t, l) | None -> t

and parse_base_type st =
  let l = loc st in
  match peek st with
  (* any Trait, or any module.Trait for a trait of an imported module *)
  | IDENT "any" when (match peek_at st 1 with IDENT s -> is_upper s || (peek_at st 2 = OP ".") | _ -> false) ->
      advance st;
      let p = parse_path st in
      let targs = parse_targs_opt st in
      TyAny (String.concat "." p, targs, l)
  | IDENT _ ->
      let p = parse_path st in
      let targs = parse_targs_opt st in
      TyPath (p, targs, l)
  | KW "fn" ->
      advance st;
      expect_op st "(";
      let ps =
        comma_list st ")" (fun st ->
            let m = if accept_kw st "mut" then MMut else if accept_kw st "take" then MTake else MBorrow in
            ignore (accept_kw st "local");
            (m, parse_type st))
      in
      expect_op st ")";
      let ret = if accept_op st "->" then Some (parse_type st) else None in
      let effs = if is_op st "!" then (advance st; Some (parse_effects ~in_type:true st)) else None in
      TyFn (ps, ret, effs, l)
  | OP "(" ->
      advance st;
      let ts = comma_list st ")" parse_type in
      expect_op st ")";
      (match ts with [ t ] -> t | _ -> TyTuple (ts, l))
  | _ -> unexpected st "a type"

and parse_path st =
  let first = ident st in
  let rec go acc =
    if is_op st "." && (match peek_at st 1 with IDENT _ -> true | _ -> false) then begin
      advance st;
      go (ident st :: acc)
    end else List.rev acc
  in
  go [ first ]

and parse_targs_opt st =
  if is_op st "[" then begin
    advance st;
    let ts = comma_list st "]" parse_targ in
    expect_op st "]";
    ts
  end else []

and parse_targ st =
  (* typestate arguments (IDENT -> IDENT) arrive with milestone 4 *)
  parse_type st

and parse_effects ?(in_type = false) st =
  (* in a function type inside a parameter list, "! pure, x: Int" ends the effects
     before the next parameter *)
  let next_is_param () =
    in_type &&
    match (peek_at st 1, peek_at st 2) with
    | IDENT _, OP (":" | "=") -> true
    | KW ("mut" | "take"), _ -> true
    | _ -> false
  in
  let rec go acc =
    let t = parse_type st in
    if is_op st "," && not (next_is_param ()) then (advance st; go (t :: acc)) else List.rev (t :: acc)
  in
  go []

(* ---------- patterns ---------- *)

let rec parse_pattern st : pattern =
  let l = loc st in
  let mk p = { p; ploc_ = l } in
  match peek st with
  | IDENT "_" -> advance st; mk PWild
  (* a variable, unless a dot follows: shapes.Circle(r) names a variant of an imported module *)
  | IDENT s when not (is_upper s) && not (peek_at st 1 = OP "." && (match peek_at st 2 with IDENT _ -> true | _ -> false)) ->
      advance st; mk (PVar s)
  | IDENT _ ->
      let path = parse_path st in
      if is_op st "(" then begin
        advance st;
        let ps = comma_list st ")" parse_pattern in
        expect_op st ")";
        mk (PCtor (path, Some ps))
      end else mk (PCtor (path, None))
  | INT s -> advance st; mk (PLit (LInt s))
  | FLOAT f -> advance st; mk (PLit (LFloat f))
  | STR s -> advance st; mk (PLit (LStr s))
  | CHAR c -> advance st; mk (PLit (LChar c))
  | KW "true" -> advance st; mk (PLit (LBool true))
  | KW "false" -> advance st; mk (PLit (LBool false))
  | OP "-" ->
      advance st;
      (match peek st with
       | INT s -> advance st; mk (PNeg (LInt s))
       | FLOAT f -> advance st; mk (PNeg (LFloat f))
       | _ -> unexpected st "a number")
  | OP "[" ->
      (* [a, b]: an array of exactly these elements; [a, b, ..]: one that starts with them *)
      advance st;
      let rec items acc =
        if is_op st "]" then (List.rev acc, false)
        else if is_op st ".." then (advance st; (List.rev acc, true))
        else begin
          let p = parse_pattern st in
          if accept_op st "," then items (p :: acc) else (List.rev (p :: acc), false)
        end in
      let ps, rest = items [] in
      expect_op st "]";
      mk (PArray (ps, rest))
  | OP "(" ->
      advance st;
      let ps = comma_list st ")" parse_pattern in
      expect_op st ")";
      (match ps with
       | [] -> mk (PLit LUnit)
       | [ p ] -> p
       | _ -> mk (PTuple ps))
  | _ -> unexpected st "a pattern"

(* ---------- expressions ---------- *)

let mk d loc = { d; loc }

(* The prelude declares built-in functions as signatures without bodies. *)
let allow_bodiless = ref false

let fragment_parser : (loc -> string -> expr) ref = ref (fun _ _ -> assert false)

let rec parse_expr st : expr =
  if is_kw st "fn" && (match peek_at st 1 with OP "(" -> true | _ -> false) then parse_lambda st
  else parse_or st

and parse_lambda st =
  let l = loc st in
  expect_kw st "fn";
  expect_op st "(";
  let ps = comma_list st ")" (parse_param ~lambda:true) in
  expect_op st ")";
  expect_op st ":";
  let e = parse_expr st in
  match peek st with
  | OP ("=" | "+=" | "-=" | "*=" | "/=" | "%=" as op) ->
      advance st;
      let rhs = parse_expr st in
      mk (Lambda (ps, LAssign (e, op, rhs))) l
  | _ -> mk (Lambda (ps, LExpr e)) l

and parse_param ?(lambda = false) st =
  let l = loc st in
  let m = if accept_kw st "mut" then MMut else if accept_kw st "take" then MTake else MBorrow in
  let name = ident st in
  let ty =
    if accept_op st ":" then (ignore (accept_kw st "local"); Some (parse_type st))
    else (if not lambda then raise (Error ("E0104", l, Printf.sprintf "parameter '%s' needs a type" name)); None)
  in
  let def = if accept_op st "=" then Some (parse_expr st) else None in
  { pmode = m; pname = name; pty = ty; pdefault = def; ploc = l }

and parse_or st =
  let l = loc st in
  let rec go lhs =
    if is_kw st "or" then (advance st; go (mk (Binop ("or", lhs, parse_and st)) l))
    (* a ?: b, right to left: what the option holds, or b, which is evaluated only then *)
    else if is_op st "?" && peek_at st 1 = OP ":" then (advance st; advance st; mk (Elvis (lhs, parse_expr st)) l)
    else lhs
  in
  go (parse_and st)

and parse_and st =
  let l = loc st in
  let rec go lhs =
    if is_kw st "and" then (advance st; go (mk (Binop ("and", lhs, parse_not st)) l)) else lhs
  in
  go (parse_not st)

and parse_not st =
  let l = loc st in
  if is_kw st "not" then (advance st; mk (Unop ("not", parse_not st)) l) else parse_cmp st

and parse_cmp st =
  let lhs = parse_set st in
  let cmp_op () = match peek st with OP ("==" | "!=" | "<" | "<=" | ">" | ">=" as o) -> Some o | _ -> None in
  match cmp_op () with
  | Some o ->
      let l = loc st in
      advance st;
      let rhs = parse_set st in
      (match cmp_op () with
       | Some _ -> fail st "comparisons do not chain; use 'and'"
       | None -> ());
      mk (Binop (o, lhs, rhs)) l
  | None -> lhs

and parse_set st =
  let rec go lhs =
    match peek st with
    | OP ("|" | "&" as o) -> let l = loc st in advance st; go (mk (Binop (o, lhs, parse_add st)) l)
    | _ -> lhs
  in
  go (parse_add st)

and parse_add st =
  let rec go lhs =
    match peek st with
    | OP ("+" | "-" | "+%" | "-%" as o) -> let l = loc st in advance st; go (mk (Binop (o, lhs, parse_mul st)) l)
    | _ -> lhs
  in
  go (parse_mul st)

and parse_mul st =
  let rec go lhs =
    match peek st with
    | OP ("*" | "/" | "%" | "*%" as o) -> let l = loc st in advance st; go (mk (Binop (o, lhs, parse_unary st)) l)
    | _ -> lhs
  in
  go (parse_unary st)

and parse_unary st =
  let l = loc st in
  match peek st with
  | OP "-" -> advance st; mk (Unop ("-", parse_unary st)) l
  | KW ("iso" | "spawn" | "try" as k) -> advance st; mk (Unop (k, parse_unary st)) l
  | _ -> parse_postfix st

and parse_postfix st =
  let rec go e =
    match peek st with
    | OP "." ->
        let l = loc st in
        advance st;
        let name = member_name st in
        go (mk (Field (e, name)) l)
    | OP "(" ->
        let l = e.loc in
        advance st;
        let args = comma_list st ")" parse_arg in
        expect_op st ")";
        go (mk (Call (e, args)) l)
    | OP "[" ->
        let l = e.loc in
        advance st;
        let bs = comma_list st "]" parse_barg in
        expect_op st "]";
        go (mk (Bracket (e, bs)) l)
    | _ -> e
  in
  go (parse_primary st)

and parse_arg st =
  let l = loc st in
  let name =
    match (peek st, peek_at st 1) with
    | IDENT s, OP "=" -> advance st; advance st; Some s
    | _ -> None
  in
  let m = if accept_kw st "mut" then Some MMut else if accept_kw st "take" then Some MTake else None in
  { aname = name; amode = m; aexpr = parse_expr st; aloc = l }

and parse_barg st =
  let looks_type =
    match peek st with
    | KW ("iso" | "frozen" | "unique") -> true
    | KW "fn" -> (match peek_at st 1 with OP "(" -> true | _ -> false) && false
    | IDENT "any" -> (match peek_at st 1 with IDENT s -> is_upper s | _ -> false)
    | IDENT s -> is_upper s
    | _ -> false
  in
  if looks_type then begin
    let save = st.pos in
    match (try Some (parse_type st) with Error _ -> None) with
    | Some t when is_op st "," || is_op st "]" -> (
        (* a bare upper-case name is ambiguous; resolution decides *)
        match t with
        | TyPath ([ n ], [], l) -> BExpr (mk (Name n) l)
        | _ -> BType t)
    | _ -> st.pos <- save; BExpr (parse_range_or_expr st)
  end else BExpr (parse_range_or_expr st)

and parse_range_or_expr st =
  let e = parse_expr st in
  if is_op st ".." then begin
    let l = loc st in
    advance st;
    mk (Range (e, parse_expr st)) l
  end else e

and parse_comps st =
  let rec go acc =
    if is_kw st "for" then begin
      advance st;
      let p = parse_pattern st in
      expect_kw st "in";
      let it = parse_range_or_expr_noif st in
      let cond = if accept_kw st "if" then Some (parse_or st) else None in
      go ({ cpat = p; citer = it; cif = cond } :: acc)
    end else List.rev acc
  in
  go []

and parse_range_or_expr_noif st = parse_range_or_expr st

and parse_primary st =
  let l = loc st in
  match peek st with
  | INT s -> advance st; mk (Lit (LInt s)) l
  | FLOAT f -> advance st; mk (Lit (LFloat f)) l
  | STR s -> advance st; mk (Lit (LStr s)) l
  | CHAR c -> advance st; mk (Lit (LChar c)) l
  | DUR (n, u) -> advance st; mk (Lit (LDur (n, u))) l
  | KW "true" -> advance st; mk (Lit (LBool true)) l
  | KW "false" -> advance st; mk (Lit (LBool false)) l
  | FSTR parts ->
      advance st;
      let ps = List.map (function RLit s -> FLit s | RExpr (src, el) -> FExpr (!fragment_parser el src)) parts in
      mk (FStr ps) l
  | IDENT s -> advance st; mk (Name s) l
  | OP "(" ->
      advance st;
      if accept_op st ")" then mk (Lit LUnit) l
      else begin
        let e = parse_expr st in
        if accept_op st ")" then e
        else begin
          expect_op st ",";
          let rest = comma_list st ")" parse_expr in
          expect_op st ")";
          mk (Tuple (e :: rest)) l
        end
      end
  | OP "[" ->
      advance st;
      if accept_op st "]" then mk (ArrayLit []) l
      else begin
        let e = parse_expr st in
        if is_kw st "for" then begin
          let cs = parse_comps st in
          expect_op st "]";
          mk (Comp (e, cs)) l
        end else if accept_op st ";" then begin
          let n = parse_expr st in
          expect_op st "]";
          mk (ArrayRepeat (e, n)) l
        end else begin
          let rest = if accept_op st "," then comma_list st "]" parse_expr else [] in
          expect_op st "]";
          mk (ArrayLit (e :: rest)) l
        end
      end
  | OP "{" ->
      advance st;
      if accept_op st "}" then mk (BraceLit []) l
      else begin
        let e = parse_expr st in
        if accept_op st ":" then begin
          let v = parse_expr st in
          if is_kw st "for" then begin
            let cs = parse_comps st in
            expect_op st "}";
            mk (MapComp (e, v, cs)) l
          end else
          let rest =
            if accept_op st "," then
              comma_list st "}" (fun st -> let k = parse_expr st in expect_op st ":"; (k, parse_expr st))
            else []
          in
          expect_op st "}";
          mk (MapLit ((e, v) :: rest)) l
        end else if is_kw st "for" then begin
          let cs = parse_comps st in
          expect_op st "}";
          mk (SetComp (e, cs)) l
        end else begin
          let rest = if accept_op st "," then comma_list st "}" parse_expr else [] in
          expect_op st "}";
          mk (BraceLit (e :: rest)) l
        end
      end
  | KW "if" ->
      advance st;
      let c = parse_expr st in
      expect_op st ":";
      let a = parse_expr st in
      expect_kw st "else";
      expect_op st ":";
      let b = parse_expr st in
      mk (IfE (c, a, b)) l
  | _ -> unexpected st "an expression"

(* ---------- statements ---------- *)

(* In `if let` and `let ... else`, a pattern that is a plain name or a tuple would match anything,
   so the form would have no point: there it stands for what an option holds, `x` for `Some(x)`. *)
let present (p : pattern) : pattern =
  match p.p with
  | PVar _ | PTuple _ -> { p with p = PCtor ([ "Some" ], Some [ p ]) }
  | _ -> p

let rec parse_block st : block =
  (* the ':' or '->' before the block has been consumed *)
  match peek st with
  | NEWLINE ->
      advance st;
      if not (is_indent st) then unexpected st "an indented block";
      advance st;
      let rec go acc =
        match peek st with
        | DEDENT -> advance st; List.rev acc
        | NEWLINE -> advance st; go acc
        | EOF -> List.rev acc
        | KW "let" ->
            (* `let PATTERN = e else ...`: what follows in the block is where the pattern matched *)
            let l = loc st in
            let s = parse_simple st in
            (match s.s with
             | Let (p, None, e) when is_kw st "else" ->
                 advance st;
                 let els = if accept_op st ":" then parse_block st else (let x = parse_simple st in expect_newline st; [ x ]) in
                 let rest = go [] in
                 let wild = { p = PWild; ploc_ = l } in
                 List.rev ({ s = Match (e, [ { apat = present p; aguard = None; abody = rest; arm_loc = l; amust_leave = false };
                                             { apat = wild; aguard = None; abody = els; arm_loc = l; amust_leave = true } ]); sloc = l } :: acc)
             | _ -> expect_newline st; go (s :: acc))
        | _ -> go (parse_stmt st :: acc)
      in
      go []
  | _ ->
      let s = parse_simple st in
      expect_newline st;
      [ s ]

and is_indent st = match peek st with INDENT -> true | _ -> false

and parse_stmt st : stmt =
  let l = loc st in
  let mks s = { s; sloc = l } in
  match peek st with
  | KW "if" when peek_at st 1 = KW "let" || binds_in_condition st ->
      (* `if PATTERN = e:` runs its block where the pattern matches, and the else where it does not.
         `if v = m.get(k):` is the commonest: v is what the option holds. `let` may be written
         before the pattern. *)
      advance st;
      ignore (accept_kw st "let");
      let p = parse_pattern st in
      expect_op st "=";
      let e = parse_expr st in
      expect_op st ":";
      let b = parse_block st in
      let els = if accept_kw st "else" then (expect_op st ":"; parse_block st) else [] in
      mks (Match (e, [ { apat = present p; aguard = None; abody = b; arm_loc = l; amust_leave = false };
                       { apat = { p = PWild; ploc_ = l }; aguard = None; abody = els; arm_loc = l; amust_leave = false } ]))
  | KW "try" when peek_at st 1 = OP ":" ->
      (* try: block, then `catch PATTERN:` blocks for its errors. An error no catch names goes on
         to the caller, as it would with no try. *)
      advance st; advance st;
      let body = parse_block st in
      let pat p = { p; ploc_ = l } in
      let rec catches acc =
        if is_ident st "catch" then begin
          let cl = loc st in
          advance st;
          let p = parse_pattern st in
          expect_op st ":";
          let b = parse_block st in
          catches ((p, b, cl) :: acc)
        end else List.rev acc in
      let cs = catches [] in
      if cs = [] then unexpected st "'catch' after the block of a try";
      let all = List.exists (fun ((p : pattern), _, _) -> match p.p with PVar _ | PWild -> true | _ -> false) cs in
      let arms =
        (* the value of the block is the value of the try, where one is wanted *)
        { apat = pat (PCtor ([ "Ok" ], Some [ pat (PVar "__value") ])); aguard = None; arm_loc = l; amust_leave = false;
          abody = [ { s = Expr (mk (Name "__value") l); sloc = l } ] }
        :: List.map (fun (p, b, cl) -> { apat = { p = PCtor ([ "Err" ], Some [ p ]); ploc_ = cl }; aguard = None; abody = b; arm_loc = cl; amust_leave = false }) cs
        @ (if all then []
           else [ { apat = pat (PCtor ([ "Err" ], Some [ pat (PVar "__uncaught") ])); aguard = None; arm_loc = l; amust_leave = false;
                    abody = [ { s = Expr (mk (Call (mk (Name "fail") l, [ { aname = None; amode = None; aexpr = mk (Name "__uncaught") l; aloc = l } ])) l); sloc = l } ] } ]) in
      mks (Match (mk (Unop ("try", mk (BlockE body) l)) l, arms))
  | KW "if" when not (is_inline_if st) ->
      advance st;
      let c = parse_expr st in
      expect_op st ":";
      let b = parse_block st in
      let rec elifs acc =
        if is_kw st "elif" then begin
          advance st;
          let c = parse_expr st in
          expect_op st ":";
          let b = parse_block st in
          elifs ((c, b) :: acc)
        end else List.rev acc
      in
      let branches = (c, b) :: elifs [] in
      let els = if accept_kw st "else" then (expect_op st ":"; Some (parse_block st)) else None in
      mks (If (branches, els))
  | KW "match" ->
      advance st;
      let e = parse_expr st in
      expect_op st ":";
      expect_newline st;
      if not (is_indent st) then unexpected st "indented match arms";
      advance st;
      let rec arms acc =
        match peek st with
        | DEDENT -> advance st; List.rev acc
        | NEWLINE -> advance st; arms acc
        | _ ->
            let al = loc st in
            let p = parse_pattern st in
            let g = if accept_kw st "if" then Some (parse_expr st) else None in
            expect_op st "->";
            let b = parse_block st in
            arms ({ apat = p; aguard = g; abody = b; arm_loc = al; amust_leave = false } :: acc)
      in
      mks (Match (e, arms []))
  | KW "par" when (match peek_at st 1 with KW "for" -> true | _ -> false) ->
      advance st; parse_for st true l
  | KW "for" -> parse_for st false l
  | KW "while" when peek_at st 1 = KW "let" || binds_in_condition st ->
      (* `while PATTERN = e:` goes round for as long as the pattern matches *)
      advance st;
      ignore (accept_kw st "let");
      let p = parse_pattern st in
      expect_op st "=";
      let e = parse_expr st in
      expect_op st ":";
      let b = parse_block st in
      mks (While (mk (Lit (LBool true)) l,
                  [ mks (Match (e, [ { apat = present p; aguard = None; abody = b; arm_loc = l; amust_leave = false };
                                     { apat = { p = PWild; ploc_ = l }; aguard = None; abody = [ mks Break ]; arm_loc = l; amust_leave = false } ])) ]))
  | KW "while" ->
      advance st;
      let c = parse_expr st in
      expect_op st ":";
      mks (While (c, parse_block st))
  | KW "fn" when (match peek_at st 1 with IDENT _ -> true | _ -> false) ->
      mks (LocalFn (parse_fn_def st []))
  | _ ->
      let s = parse_simple st in
      expect_newline st;
      s

(* whether the condition of an if or a while has a `=` of its own, outside any brackets: it then
   binds a pattern, since a condition that is an expression has none *)
and binds_in_condition st =
  let rec scan k depth =
    match peek_at st k with
    | NEWLINE | INDENT | DEDENT | EOF -> false
    | OP ("(" | "[" | "{") -> scan (k + 1) (depth + 1)
    | OP (")" | "]" | "}") -> scan (k + 1) (depth - 1)
    | OP "=" when depth = 0 -> true
    | OP ":" when depth = 0 -> false
    | _ -> scan (k + 1) depth
  in
  scan 1 0

(* "if c: a else: b" on one line in statement position is an if statement whose
   blocks are simple statements; both parse the same way. *)
and is_inline_if st =
  let rec scan k depth =
    match peek_at st k with
    | NEWLINE | INDENT | DEDENT | EOF -> false
    | OP ("(" | "[" | "{") -> scan (k + 1) (depth + 1)
    | OP (")" | "]" | "}") -> scan (k + 1) (depth - 1)
    | KW "else" when depth = 0 -> true
    | _ -> scan (k + 1) depth
  in
  scan 1 0

and parse_for st par l =
  expect_kw st "for";
  let p = parse_pattern st in
  expect_kw st "in";
  let m = if accept_kw st "mut" then MMut else if accept_kw st "take" then MTake else MBorrow in
  let it = parse_range_or_expr st in
  expect_op st ":";
  { s = For (par, p, m, it, parse_block st); sloc = l }

and parse_simple st : stmt =
  let l = loc st in
  let mks s = { s; sloc = l } in
  match peek st with
  | KW "let" ->
      advance st;
      let p = parse_pattern st in
      let t = if accept_op st ":" then Some (parse_type st) else None in
      expect_op st "=";
      mks (Let (p, t, parse_expr st))
  | KW "shared" | KW "var" ->
      let shared = accept_kw st "shared" in
      expect_kw st "var";
      let n = ident st in
      let t = if accept_op st ":" then Some (parse_type st) else None in
      expect_op st "=";
      mks (Var (shared, n, t, parse_expr st))
  | KW "return" ->
      advance st;
      (match peek st with
       | NEWLINE | DEDENT | EOF -> mks (Return None)
       | _ -> mks (Return (Some (parse_expr st))))
  | KW "break" -> advance st; mks Break
  | KW "continue" -> advance st; mks Continue
  | KW "check" -> advance st; mks (Check (parse_expr st))
  | KW "lend" ->
      advance st;
      let m = accept_kw st "mut" in
      mks (Lend (m, parse_postfix st))
  | KW "resume" ->
      advance st;
      (match peek st with
       | NEWLINE | DEDENT | EOF -> mks (Resume None)
       | _ -> mks (Resume (Some (parse_expr st))))
  | IDENT "assert" when not (is_op_at st 1 ["="; "."]) ->
      advance st; mks (Assert (parse_expr st))
  | IDENT "assert_fails" when is_op_at st 1 [ "[" ] ->
      advance st;
      expect_op st "[";
      let t = parse_type st in
      expect_op st "]";
      mks (AssertFails (t, parse_expr st))
  | IDENT "assert_snapshot" when not (is_op_at st 1 ["="; "."]) ->
      advance st; mks (AssertSnapshot (parse_expr st))
  | _ ->
      let e = parse_expr st in
      (match peek st with
       | OP ("=" | "+=" | "-=" | "*=" | "/=" | "%=" as op) ->
           advance st;
           mks (Assign (e, op, parse_expr st))
       | _ -> mks (Expr e))

and is_op_at st k ops = match peek_at st k with OP o -> List.mem o ops | _ -> false

(* ---------- items ---------- *)

and parse_generics st =
  if is_op st "[" then begin
    advance st;
    let gs =
      comma_list st "]" (fun st ->
          let l = loc st in
          let n = ident st in
          let bounds =
            if accept_op st ":" then begin
              let rec go acc =
                let t = parse_type st in
                if accept_op st "+" then go (t :: acc) else List.rev (t :: acc)
              in
              go []
            end else []
          in
          { gname = n; gbounds = bounds; gloc = l })
    in
    expect_op st "]";
    gs
  end else []

and parse_fn_sig st mods =
  let l = loc st in
  expect_kw st "fn";
  let name = member_name st in
  let export = accept_op st "*" in
  let gens = parse_generics st in
  expect_op st "(";
  let ps = comma_list st ")" (parse_param ~lambda:false) in
  expect_op st ")";
  let ret, lend =
    if accept_op st "->" then
      if accept_kw st "lend" then
        let m = accept_kw st "mut" in
        (Some (parse_type st), Some (if m then "lend mut" else "lend"))
      else (Some (parse_type st), None)
    else (None, None)
  in
  let effs = if accept_op st "!" then Some (parse_effects st) else None in
  let wh = if accept_kw st "where" then Some (parse_expr st) else None in
  let ens = if accept_kw st "ensures" then Some (parse_expr st) else None in
  { fname = name; fexport = export; fmods = mods; fgenerics = gens; fparams = ps; fret = ret;
    fret_lend = lend; feffects = effs; fwhere = wh; fensures = ens; fbody = None; floc = l }

and parse_fn_def st mods =
  let sg = parse_fn_sig st mods in
  if !allow_bodiless && not (is_op st ":") then (expect_newline st; sg) else begin
  expect_op st ":";
  { sg with fbody = Some (parse_block st) } end

let fn_mods = [ "inplace"; "total"; "noalloc"; "strict"; "trusted" ]

(* the struct just read was written as a block, which ends its own line *)
let block_struct = ref false
(* the field of a variant written `from T`: an error of type T becomes that variant where it is
   propagated, as if `impl From[T]` had been written *)
let from_marker = "__from"

let parse_fields st =
  comma_list st ")" (fun st ->
      let l = loc st in
      let name =
        match (peek st, peek_at st 1) with
        | IDENT s, OP ":" when not (is_upper s) -> advance st; advance st; Some s
        | IDENT "from", (IDENT _ | OP "(" | OP "[") -> advance st; Some from_marker
        | _ -> None
      in
      let t = parse_type st in
      let d = if accept_op st "=" then Some (parse_expr st) else None in
      { fdname = name; fdty = t; fddefault = d; fdloc = l })

let parse_type_body st =
  match peek st with
  | KW "struct" when peek_at st 1 = OP ":" ->
      (* a field to a line: struct: then `name: Type` lines, each with an optional default *)
      advance st; advance st;
      expect_newline st;
      if not (is_indent st) then unexpected st "indented fields";
      advance st;
      let rec fields acc =
        match peek st with
        | DEDENT -> advance st; List.rev acc
        | NEWLINE -> advance st; fields acc
        | _ ->
            let l = loc st in
            let n = ident st in
            expect_op st ":";
            let t = parse_type st in
            let d = if accept_op st "=" then Some (parse_expr st) else None in
            expect_newline st;
            fields ({ fdname = Some n; fdty = t; fddefault = d; fdloc = l } :: acc) in
      block_struct := true;
      BStruct (fields [])
  | KW "struct" ->
      advance st;
      expect_op st "(";
      let fs = parse_fields st in
      expect_op st ")";
      BStruct fs
  | IDENT s when is_upper s && (match peek_at st 1 with OP ("(" | "|") | NEWLINE | DEDENT | EOF | KW "where" -> true | _ -> false) ->
      let rec variants acc =
        let l = loc st in
        let n = ident st in
        let fs =
          if accept_op st "(" then (let fs = parse_fields st in expect_op st ")"; Some fs) else None
        in
        let v = { vname = n; vfields = fs; vloc = l } in
        if accept_op st "|" then variants (v :: acc) else List.rev (v :: acc)
      in
      BData (variants [])
  | _ -> BAlias (parse_type st)

let parse_item st : item =
  let l = loc st in
  match peek st with
  | KW "import" ->
      advance st;
      let p = parse_path st in
      let alias = if accept_kw st "as" then Some (ident st) else None in
      expect_newline st;
      IImport (p, alias, l)
  | KW "let" ->
      advance st;
      let n = ident st in
      let ex = accept_op st "*" in
      let t = if accept_op st ":" then Some (parse_type st) else None in
      expect_op st "=";
      let e = parse_expr st in
      expect_newline st;
      IConst (n, ex, t, e, l)
  | IDENT "test" when (match peek_at st 1 with STR _ | IDENT "rejects" -> true | _ -> false) ->
      advance st;
      let rej =
        if is_ident st "rejects" then begin
          advance st;
          match peek st with
          | IDENT c -> advance st; Some c
          | _ -> unexpected st "a diagnostic code"
        end else None
      in
      let name = match peek st with STR s -> advance st; s | _ -> unexpected st "a test name" in
      (* a property test: for x: T, y: U [where cond] *)
      let params, cond =
        if accept_kw st "for" then begin
          let rec more acc =
            let p = parse_param st in
            if p.pmode <> MBorrow then raise (Error ("E0100", p.ploc, "an input of a property test is written `name: Type`"));
            if accept_op st "," then more (p :: acc) else List.rev (p :: acc) in
          let ps = more [] in
          let cond = if is_ident st "where" || is_kw st "where" then (advance st; Some (parse_expr st)) else None in
          (ps, cond)
        end else ([], None) in
      expect_op st ":";
      ITest { tsname = name; tsrejects = rej; tsparams = params; tswhere = cond; tsbody = parse_block st; tsloc = l }
  | KW "trait" ->
      advance st;
      let n = ident st in
      let ex = accept_op st "*" in
      let gens = parse_generics st in
      expect_op st ":";
      expect_newline st;
      if not (is_indent st) then unexpected st "indented trait methods";
      advance st;
      let rec go acc =
        match peek st with
        | DEDENT -> advance st; List.rev acc
        | NEWLINE -> advance st; go acc
        | _ ->
            let sg = parse_fn_sig st [] in
            let sg = if accept_op st ":" then { sg with fbody = Some (parse_block st) } else (expect_newline st; sg) in
            go (sg :: acc)
      in
      ITrait { trname = n; trexport = ex; trgenerics = gens; trmethods = go []; trloc = l }
  | KW "impl" ->
      advance st;
      let gens = parse_generics st in
      let tr = parse_path st in
      let targs = parse_targs_opt st in
      expect_kw st "for";
      let fty = parse_type st in
      let methods =
        if accept_op st ":" then begin
          expect_newline st;
          if not (is_indent st) then unexpected st "indented methods";
          advance st;
          let rec go acc =
            match peek st with
            | DEDENT -> advance st; List.rev acc
            | NEWLINE -> advance st; go acc
            | _ ->
                let rec mods acc = match peek st with IDENT m when List.mem m fn_mods -> advance st; mods (m :: acc) | _ -> List.rev acc in
                let ms = mods [] in
                go (parse_fn_def st ms :: acc)
          in
          go []
        end else (expect_newline st; [])
      in
      IImpl { igenerics = gens; itrait = tr; itargs = targs; ifor = fty; imethods = methods; iloc = l }
  | _ ->
      (* fn or type definitions, with modifiers *)
      let rec mods acc =
        match (peek st, peek_at st 1) with
        | IDENT m, (KW "fn" | IDENT _) when List.mem m fn_mods -> advance st; mods (m :: acc)
        | _ -> List.rev acc
      in
      let ms = mods [] in
      if is_kw st "fn" then IFn (parse_fn_def st ms)
      else begin
        let repr =
          if is_ident st "repr" && (match peek_at st 1 with OP "(" -> true | _ -> false) then begin
            advance st; expect_op st "(";
            let r = ident st in
            expect_op st ")"; expect_newline st; Some r
          end else None
        in
        let resource = accept_kw st "resource" in
        let opn = if is_ident st "open" && (match peek_at st 1 with KW "type" -> true | _ -> false) then (advance st; true) else false in
        if not (is_kw st "type") then unexpected st "an item (fn, type, trait, impl, let, import or test)";
        advance st;
        let n = ident st in
        let ex = accept_op st "*" in
        let gens = parse_generics st in
        let ended = ref false in
        let body =
          if accept_op st "=" then begin
            match peek st with
            | NEWLINE when (match peek_at st 1 with INDENT -> true | _ -> false) ->
                advance st; advance st;
                let b = parse_type_body st in
                expect_newline st;
                (match peek st with DEDENT -> advance st | _ -> unexpected st "end of type definition");
                ended := true;
                b
            | _ ->
                block_struct := false;
                let b = parse_type_body st in
                if !block_struct then ended := true;
                b
          end else BNone
        in
        let wh = if accept_kw st "where" then Some (parse_expr st) else None in
        ignore wh;
        if not !ended then expect_newline st;
        IType { tname = n; texport = ex; tresource = resource; topen = opn; trepr = repr;
                tgenerics = gens; tbody = body; tloc = l }
      end

let parse_tokens file toks =
  let st = { toks; pos = 0; file } in
  let rec go acc =
    match peek st with
    | EOF -> List.rev acc
    | NEWLINE -> advance st; go acc
    | _ ->
        let item = parse_item st in
        (* `V(from T)` in a data type: the variant holds a T, and an error of type T becomes it *)
        (match item with
         | IType ({ tbody = BData vs; _ } as td) when List.exists (fun (v : variant) -> match v.vfields with Some fs -> List.exists (fun f -> f.fdname = Some from_marker) fs | None -> false) vs ->
             let impls = ref [] in
             let vs = List.map (fun (v : variant) ->
                 match v.vfields with
                 | Some [ ({ fdname = Some m; _ } as f) ] when m = from_marker ->
                     if td.tgenerics <> [] then raise (Error ("E0100", v.vloc, "'from' in a variant is not available in a type with type parameters; write the impl of From"));
                     let l = v.vloc in
                     let self = TyPath ([ td.tname ], [], l) in
                     let body = [ { s = Expr (mk (Call (mk (Name v.vname) l, [ { aname = None; amode = None; aexpr = mk (Name "x") l; aloc = l } ])) l); sloc = l } ] in
                     let fd = { fname = "from"; fexport = false; fmods = []; fgenerics = [];
                                fparams = [ { pmode = MBorrow; pname = "x"; pty = Some f.fdty; pdefault = None; ploc = l } ];
                                fret = Some self; fret_lend = None; feffects = None; fwhere = None; fensures = None; fbody = Some body; floc = l } in
                     impls := IImpl { igenerics = []; itrait = [ "From" ]; itargs = [ f.fdty ]; ifor = self; imethods = [ fd ]; iloc = l } :: !impls;
                     { v with vfields = Some [ { f with fdname = None } ] }
                 | Some fs when List.exists (fun f -> f.fdname = Some from_marker) fs ->
                     raise (Error ("E0100", v.vloc, "a variant written with 'from' holds that one value and nothing else"))
                 | _ -> v) vs in
             go (!impls @ (IType { td with tbody = BData vs } :: acc))
         | _ -> go (item :: acc))
  in
  { items = go []; path = file }

let parse_file file src = parse_tokens file (Lexer.tokenize file src)

let () =
  fragment_parser :=
    fun l src ->
      let st = { toks = Lexer.tokenize_fragment l src; pos = 0; file = l.file } in
      let e = parse_expr st in
      (match peek st with EOF -> () | _ -> unexpected st "'}' to end the interpolation");
      e
