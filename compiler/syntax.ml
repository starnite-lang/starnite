(* SPDX-License-Identifier: GPL-3.0-or-later *)
(* Syntax tree produced by pass 1 (section 2). *)

type loc = { file : string; line : int; col : int }

let noloc = { file = "<builtin>"; line = 0; col = 0 }

exception Error of string * loc * string (* code, location, message *)

let error code loc fmt = Printf.ksprintf (fun m -> raise (Error (code, loc, m))) fmt

(* a program that is valid but uses something a backend does not support yet *)
exception Unsupported of string * loc

type mode = MBorrow | MMut | MTake

type ty =
  | TyPath of string list * ty list * loc        (* Array[Int], geometry.Vec3 *)
  | TyAny of string * ty list * loc              (* any Figure *)
  | TyFn of (mode * ty) list * ty option * ty list option * loc
      (* params, return, effects (None = effect-polymorphic) *)
  | TyTuple of ty list * loc                     (* () is Unit *)
  | TyOpt of ty * loc                            (* T? *)
  | TyQual of string * ty * loc                  (* iso / frozen / unique *)

let ty_loc = function
  | TyPath (_, _, l) | TyAny (_, _, l) | TyFn (_, _, _, l) | TyTuple (_, l)
  | TyOpt (_, l) | TyQual (_, _, l) -> l

type lit =
  | LInt of string      (* raw text, underscores removed *)
  | LFloat of float
  | LStr of string
  | LChar of int
  | LBool of bool
  | LUnit
  | LDur of int64 * string   (* value, unit *)

type expr = { d : expr_d; loc : loc }

and expr_d =
  | Lit of lit
  | FStr of fpart list
  | Name of string
  | Field of expr * string
  | Call of expr * arg list
  | Bracket of expr * barg list
  | Tuple of expr list
  | ArrayLit of expr list
  | ArrayRepeat of expr * expr                   (* [x; n]: n copies of x *)
  | Comp of expr * comp list
  | BraceLit of expr list                        (* set literal (milestone 2) *)
  | MapLit of (expr * expr) list                 (* map literal (milestone 2) *)
  | IfE of expr * expr * expr
  | Lambda of param list * lambda_body
  | Binop of string * expr * expr
  | Unop of string * expr                        (* "-", "not", "try", "iso", "spawn" *)
  | Range of expr * expr

and fpart = FLit of string | FExpr of expr

and arg = { aname : string option; amode : mode option; aexpr : expr; aloc : loc }

and barg = BExpr of expr | BType of ty

and comp = { cpat : pattern; citer : expr; cif : expr option }

and lambda_body = LExpr of expr | LAssign of expr * string * expr

and param = {
  pmode : mode;
  pname : string;
  pty : ty option;
  pdefault : expr option;
  ploc : loc;
}

and pattern = { p : pattern_d; ploc_ : loc }

and pattern_d =
  | PWild
  | PVar of string
  | PLit of lit
  | PNeg of lit                                   (* -1 in a pattern *)
  | PCtor of string list * pattern list option   (* None = no parentheses *)
  | PTuple of pattern list

type stmt = { s : stmt_d; sloc : loc }

and stmt_d =
  | Let of pattern * ty option * expr
  | Var of bool * string * ty option * expr       (* shared? *)
  | Assign of expr * string * expr                (* place, op ("=", "+=", ...), value *)
  | Return of expr option
  | Break
  | Continue
  | Check of expr
  | Lend of bool * expr
  | Resume of expr option
  | Assert of expr
  | AssertFails of ty * expr
  | AssertSnapshot of expr
  | Expr of expr
  | If of (expr * block) list * block option
  | Match of expr * arm list
  | For of bool * pattern * mode * expr * block   (* par?, pattern, mode, iterable *)
  | While of expr * block
  | LocalFn of fn_def

and block = stmt list

and arm = { apat : pattern; aguard : expr option; abody : block; arm_loc : loc }

and fn_def = {
  fname : string;
  fexport : bool;
  fmods : string list;
  fgenerics : gparam list;
  fparams : param list;
  fret : ty option;
  fret_lend : string option;       (* Some "lend" / Some "lend mut" *)
  feffects : ty list option;       (* None = no ! list written *)
  fwhere : expr option;
  fensures : expr option;
  fbody : block option;
  floc : loc;
}

and gparam = { gname : string; gbounds : ty list; gloc : loc }

type field = { fdname : string option; fdty : ty; fddefault : expr option; fdloc : loc }

type variant = { vname : string; vfields : field list option; vloc : loc }

type type_body =
  | BStruct of field list
  | BData of variant list
  | BAlias of ty
  | BNone

type type_def = {
  tname : string;
  texport : bool;
  tresource : bool;
  topen : bool;
  trepr : string option;
  tgenerics : gparam list;
  tbody : type_body;
  tloc : loc;
}

type trait_def = {
  trname : string;
  trexport : bool;
  trgenerics : gparam list;
  trmethods : fn_def list;
  trloc : loc;
}

type impl_def = {
  igenerics : gparam list;
  itrait : string list;
  itargs : ty list;
  ifor : ty;
  imethods : fn_def list;
  iloc : loc;
}

type test_def = {
  tsname : string;
  tsrejects : string option;
  tsbody : block;
  tsloc : loc;
}

type item =
  | IFn of fn_def
  | IType of type_def
  | ITrait of trait_def
  | IImpl of impl_def
  | IConst of string * bool * ty option * expr * loc
  | ITest of test_def
  | IImport of string list * string option * loc

type file = { items : item list; path : string }
