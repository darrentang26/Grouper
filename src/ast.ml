(* Abstract Syntax Tree and functions for printing it *)

type op = Add | Sub | Mult | Div | Equal | Neq | Less | Leq | Greater | Geq |
          And | Or

type uop = Neg | Not

type name = Name of string

type typ = 
    Int | Bool | Float | Void | String
  | UTyp of (name * typ) list
  | FTyp of typ list * typ
  | PairType of typ * typ
  | ListType of typ

type typ_decl = name * typ

type bind = name * typ

type expr =
    Literal of int
  | Fliteral of string
  | BoolLit of bool
  | StringLit of string
  | PairExpr of expr * expr
  | ListExpr of expr list
  | Var of name
  | Binop of expr * op * expr
  | Unop of uop * expr
  | Let of (bind * expr) list * expr
  | Function of name list * expr
  | Match of name list * (pattern * expr) list
  | Call of expr * expr
  | If of expr * expr * expr
  | Noexpr

and pattern =  
    Pattern of target list

and target = 
    TargetName of name
  | TargetExpr of expr
  | TargetApp of name * target
  | CatchAll

type strct = Struct of (bind * expr) list

type program = typ_decl list * expr
