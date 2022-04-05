(* Semantically-checked Abstract Syntax Tree and functions for printing it *)

open Ast

type sexpr = type_expr * sx     
and sx =
    SLiteral of int
  | SFliteral of string
  | SBoolLit of bool
  | SStringLit of string
  | SPairExpr of sexpr * sexpr
  | SConsExpr of sexpr * sexpr
  | SEmptyListExpr
  | SName of name
  | SBinop of sexpr * op * sexpr
  | SUnop of uop * sexpr
  | SLet of (bind * sexpr) list * sexpr
  | SFunction of bind * sexpr (* After semanting, functions are all curried *)
  | SAdtExpr of target_concrete
  | SStructInit of (name * sexpr) list
  | SStructRef of name * name
  | SMatch of name list * (pattern * sexpr) list
  | SCall of sexpr * sexpr
  | SIf of sexpr * sexpr * sexpr
  | SGroup of sgroup
  | SRing of sring
  | SField of sfield
  | SPrint of sexpr

and spattern =  
    SPattern of starget_wild list

and starget_wild = 
    STargetWildName of name
  | STargetWildLiteral of sexpr
  | STargetWildApp of name * starget_wild
  | SCatchAll

and starget_concrete = 
    STargetConcName of name
  | STargetConcExpr of sexpr
  | STargetConcApp of name * starget_concrete
  
and sgroup = type_expr * sexpr * sexpr * sexpr * sexpr
and sring = type_expr * sexpr * sexpr * sexpr * sexpr * sexpr * sexpr
and sfield = type_expr * sexpr * sexpr * sexpr * sexpr * sexpr * sexpr * sexpr

type sprogram = typ_decl list * sexpr

(* Pretty-printing functions *)

let rec string_of_sexpr (t, e) =
  "(" ^ string_of_type_expr t ^ " : " ^ (match e with 
  SLiteral(lit) -> string_of_int lit
| SFliteral(str) -> str
| SBoolLit(true) -> "true"
| SBoolLit(false) -> "false"
| SStringLit(str) -> "\"" ^ str ^ "\""
| SPairExpr(expr1, expr2) -> "(" ^ string_of_sexpr expr1 ^ "," ^ string_of_sexpr expr2 ^ ")"
| SConsExpr(expr1, expr2) -> "(" ^ string_of_sexpr expr1 ^ " :: " ^ string_of_sexpr expr2 ^ ")"
| SEmptyListExpr -> "[]"
| SName(name) -> name
| SBinop(expr1,op,expr2) -> string_of_sexpr expr1 ^ " "  ^ string_of_op op ^ " " ^ string_of_sexpr expr2
| SUnop(op,expr) -> string_of_uop op ^ string_of_sexpr expr
| SLet(binds, body) -> "let " ^ String.concat " and " (List.map (fun (bind, expr) -> string_of_bind bind ^ " = " ^ string_of_sexpr expr) binds) ^ " in " ^ (string_of_sexpr body)
| SFunction((name, ty), body) -> "(" ^ string_of_type_expr ty ^ " " ^ name ^ ") -> " ^ string_of_sexpr body 
| SAdtExpr(target) -> string_of_target_concrete target
| SStructInit(attribs) -> "{" ^ String.concat ", " (List.map (fun (name,expr) -> name ^ " = " ^ string_of_sexpr expr) attribs ) ^ "}"
| SStructRef(name1, name2) -> name1 ^ "." ^ name2
| SMatch(namelist, patexprlist) -> "match (" ^ String.concat " " (List.map (fun (name) -> name) namelist) ^ ")" ^ " with\n  | "
                                ^ String.concat "\n  | " (List.map (fun (pattern, expr) -> string_of_pattern pattern 
                                ^ " -> " ^ string_of_sexpr expr) patexprlist)
| SCall(expr1, expr2) -> string_of_sexpr expr1 ^ " " ^ string_of_sexpr expr2
| SIf(expr1,expr2,expr3) -> "if " ^ string_of_sexpr expr1 
                         ^ " then " ^ string_of_sexpr expr2 
                         ^ " else " ^ string_of_sexpr expr3
| SGroup(group) -> string_of_sgroup group
| SRing(ring) -> string_of_sring ring
| SField(field) -> string_of_sfield field
| SPrint(expr) -> "print: " ^ string_of_sexpr expr
  ) ^ ")"
and string_of_spattern = function
  SPattern(targets) -> "(" ^ String.concat ", " (List.map string_of_starget_wild targets) ^ ")"  

and string_of_starget_wild = function
  STargetWildName(name) -> name
| STargetWildLiteral(expr) -> string_of_sexpr expr
| STargetWildApp(name,target) -> name ^ "(" ^ string_of_starget_wild target ^ ")"
| SCatchAll -> "_"

and string_of_starget_concrete = function
  STargetConcName(name) -> name
| STargetConcExpr(expr) -> string_of_sexpr expr
| STargetConcApp(name, target) -> name ^ string_of_starget_concrete target  

and string_of_sgroup (name, expr1, expr2, expr3, expr4) = 
  string_of_type_expr name ^ " " ^
  string_of_sexpr expr1 ^ " " ^
  string_of_sexpr expr2 ^ " " ^
  string_of_sexpr expr3 ^ " " ^
  string_of_sexpr expr4

and string_of_sring(name, expr1, expr2, expr3, expr4, expr5, expr6) = 
  string_of_sgroup (name, expr1, expr2, expr3, expr4) ^ " " ^
  string_of_sexpr expr5 ^ " " ^
  string_of_sexpr expr6

and string_of_sfield(name, expr1, expr2, expr3, expr4, expr5, expr6, expr7) = 
  string_of_sring (name, expr1, expr2, expr3, expr4, expr5, expr6) ^ " " ^
  string_of_sexpr expr7

let string_of_sprogram (typ_decls, expr) = 
  String.concat "" (List.map string_of_typ_decl typ_decls) ^ string_of_sexpr expr ^ "\n"
