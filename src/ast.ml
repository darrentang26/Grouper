(* Abstract Syntax Tree and functions for printing it *)

type op = Add | Sub | Mult | Div | Equal | Neq | Less | Leq | Greater | Geq |
          And | Or

type uop = Neg | Not

type name = Name of string

(* these types can occur before assignments *)
type type_name = 
    IntName | BoolName | FloatName | VoidName | StringName
  | UserTypeName of name
  | FunTypeName of type_name list * type_name
  | PairTypeName of type_name * type_name
  | ListTypeName of type_name
  | GroupTypeName of type_name
  | RingTypeName of type_name
  | FieldTypeName of type_name

(* these types can occur in type definitions *)
type type_expr = 
    IntExpr | BoolExpr | FloatExpr | VoidExpr | StringExpr
  | AdtTypeExpr of (name * type_name) list
  | StructTypeExpr of (name * type_name) list
  | FunType of type_expr list * type_expr
  | PairType of type_expr * type_expr
  | ListType of type_expr
  | GroupType of type_expr
  | RingType of type_expr
  | FieldType of type_expr

type typ_decl = name * type_expr

type bind = name * type_name

type group = type_name * expr * expr * expr * expr
type ring = group * expr * expr
type field = ring * expr

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
  | AdtExpr of target_concrete
  | StructInit of (name * expr) list
  | StructRef of name * name
  | Match of name list * (pattern * expr) list
  | Call of expr * expr
  | If of expr * expr * expr
  | Group of group
  | Ring of ring
  | Field of field
  | Print of expr
  | Noexpr

and pattern =  
    Pattern of target_wild list

and target_wild = 
    TargetWildName of name
  | TargetWildExpr of expr
  | TargetWildApp of name * target_wild
  | CatchAll

and target_concrete = 
    TargetConcName of name
  | TargetConcExpr of expr
  | TargetConcApp of name * target_concrete

type program = typ_decl list * expr
