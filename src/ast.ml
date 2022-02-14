type unop = Neg | Not

type binop = Add | Sub | Mul | Div 
              | Equal | Neq 
              | Less | Leq 
              | Geq | Greater

type typ =  Int | Bool | Function 

type bind = typ * string


type expr =
  Binop of expr * operator * expr
| Lit of int
| Seq of expr * expr
| Asn of string * expr
| Var of string