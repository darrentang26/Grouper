(* Abstract Syntax Tree and functions for printing it *)

type op = Add | Sub | Mult | Div | Equal | Neq | Less | Leq | Greater | Geq |
          And | Or

type uop = Neg | Not

type name = Name of string

type typ = 
  Int | Bool | Float | Void | String
  | UTyp of (name * typ) list
  | FTyp of typ list * typ
  | Pair of typ * typ
  | List of typ

type typ_decl = name * typ

type bind = name * typ

type expr =
Literal of int
| Fliteral of string
| BoolLit of bool
| Var of name
| Binop of expr * op * expr
| Unop of uop * expr
| Let of (bind * expr) list * expr
| Fun of bind list * typ * expr
| Call of name * expr list
| If of expr * expr * expr
| Noexpr

type strct = Struct of (bind * expr) list

type program = typ_decl list * expr
