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
  | SCarExpr of sexpr
  | SCdrExpr of sexpr
  | SEmptyListExpr
  | SName of name
  | SBinop of sexpr * op * sexpr
  | SUnop of uop * sexpr
  | SLet of (bind * sexpr) list * sexpr
  | SFunction of bind list * sexpr
  | SAdtExpr of starget
  | SStructInit of (name * sexpr) list
  | SStructRef of name * name
  | SMatch of bind list * (spattern * sexpr) list
  | SCall of sexpr * sexpr list
  | SIf of sexpr * sexpr * sexpr
  | SPrint of sexpr

and spattern =  
    SPattern of starget list

and starget = 
    STargetWildName of name
  | STargetWildLiteral of sexpr
  | STargetWildApp of name * starget
  | SCatchAll

type sprogram = typ_decl list * sexpr
type sprogram_lifted = typ_decl list * (bind * sexpr) list * sexpr

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
| SCarExpr(expr) -> "car " ^ string_of_sexpr expr
| SCdrExpr(expr) -> "cdr " ^ string_of_sexpr expr
| SEmptyListExpr -> "[]"
| SName(name) -> name
| SBinop(expr1,op,expr2) -> string_of_sexpr expr1 ^ " "  ^ string_of_op op ^ " " ^ string_of_sexpr expr2
| SUnop(op,expr) -> string_of_uop op ^ string_of_sexpr expr
| SLet(binds, body) -> "let " ^ String.concat "\nand " (List.map (fun (bind, expr) -> string_of_bind bind ^ " =\n" ^ string_of_sexpr expr) binds) ^ "\nin " ^ (string_of_sexpr body)
| SFunction(args,body) -> "(" ^ String.concat ", " (List.map string_of_bind args) ^ ") -> " ^ string_of_sexpr body 
| SAdtExpr(target) -> string_of_starget target
| SStructInit(attribs) -> "{" ^ String.concat ", " (List.map (fun (name,expr) -> name ^ " = " ^ string_of_sexpr expr) attribs ) ^ "}"
| SStructRef(name1, name2) -> name1 ^ "." ^ name2
| SMatch(args, patexprlist) -> "match (" ^ String.concat ", " (List.map string_of_bind args) ^ ")" ^ " with\n  | "
                                ^ String.concat "\n  | " (List.map (fun (pattern, expr) -> string_of_spattern pattern 
                                ^ " -> " ^ string_of_sexpr expr) patexprlist)
| SCall(expr1, expr2s) -> string_of_sexpr expr1 ^ ": {" ^ String.concat ", " (List.map string_of_sexpr expr2s) ^ "}"
| SIf(expr1,expr2,expr3) -> "if " ^ string_of_sexpr expr1 
                         ^ " then " ^ string_of_sexpr expr2 
                         ^ " else " ^ string_of_sexpr expr3
| SPrint(expr) -> "print: " ^ string_of_sexpr expr
  ) ^ ")"
and string_of_spattern = function
  SPattern(targets) -> "(" ^ String.concat ", " (List.map string_of_starget targets) ^ ")"  

and string_of_starget = function
  STargetWildName(name) -> name
| STargetWildLiteral(expr) -> string_of_sexpr expr
| STargetWildApp(name,target) -> name ^ "(" ^ string_of_starget target ^ ")"
| SCatchAll -> "_" 

let string_of_sprogram (typ_decls, expr) = 
  String.concat "" (List.map string_of_typ_decl typ_decls) ^ string_of_sexpr expr ^ "\n"

let string_of_sprogram_lifted (typ_decls, fs, expr) =
  String.concat "" (List.map string_of_typ_decl typ_decls) ^ "\n" ^
  String.concat "\n" (List.map (fun (bind, sexpr) -> string_of_bind bind ^ ": " ^ string_of_sexpr sexpr) fs) ^ "\n\n" ^
  string_of_sexpr expr ^ "\n"
