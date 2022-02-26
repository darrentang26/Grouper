(* Abstract Syntax Tree and functions for printing it *)

type op = Add | Sub | Mult | Div | Equal | Neq | Less | Leq | Greater | Geq |
          And | Or | Cons

type uop = Neg | Not

type name = string

(* these types can occur before assignments *)
type type_name = 
    IntName | BoolName | FloatName | VoidName | StringName
  | UserTypeName of name
  | FunTypeName of type_name * type_name
  | PairTypeName of type_name * type_name
  | ListTypeName of type_name
  | GroupTypeName of type_name
  | RingTypeName of type_name
  | FieldTypeName of type_name
  | PolyTypeName of type_name

(* these types can occur in type definitions *)
type type_expr = 
    IntExpr | BoolExpr | FloatExpr | VoidExpr | StringExpr
  | AdtTypeExpr of (name * type_name) list
  | StructTypeExpr of (name * type_name) list
  | FunType of type_expr * type_expr
  | PairType of type_expr * type_expr
  | ListType of type_expr
  | GroupType of type_expr
  | RingType of type_expr
  | FieldType of type_expr
  | PolyType of type_expr

type typ_decl = name * type_expr

type bind = name * type_name

type expr =
    Literal of int
  | Fliteral of string
  | BoolLit of bool
  | StringLit of string
  | PairExpr of expr * expr
  | ListExpr of expr list
  | Name of name
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

and pattern =  
    Pattern of target_wild list

and target_wild = 
    TargetWildName of name
  | TargetWildLiteral of expr
  | TargetWildApp of name * target_wild
  | CatchAll

and target_concrete = 
    TargetConcName of name
  | TargetConcExpr of expr
  | TargetConcApp of name * target_concrete
  
and group = type_name * expr * expr * expr * expr
and ring = type_name * expr * expr * expr * expr * expr * expr
and field = type_name * expr * expr * expr * expr * expr * expr * expr

type program = typ_decl list * expr

(* AST nodes to strings *)
let string_of_op = function
  Add -> "+"
| Sub -> "-"
| Mult -> "*"
| Div -> "/"
| Equal -> "=="
| Neq -> "!="
| Less -> "<"
| Leq -> "<="
| Greater -> ">"
| Geq -> ">=" 
| And -> "&&"
| Or -> "||"
| Cons -> "::"

let string_of_uop = function
  Neg -> "-"
| Not -> "!"

let rec string_of_type_name = function
  IntName -> "int"
| FloatName -> "float"
| BoolName -> "bool"
| StringName -> "string"
| VoidName -> "void"
| UserTypeName(name) -> name
| FunTypeName(name1, name2) -> string_of_type_name name1 ^ " -> " ^ string_of_type_name name2 
| PairTypeName(tyname1, tyname2) -> "(" ^ string_of_type_name tyname1 ^ " * " ^ string_of_type_name tyname2 ^ ")"
| ListTypeName(tyname) -> string_of_type_name tyname ^ " list"
| GroupTypeName(tyname) -> string_of_type_name tyname ^ " group"
| RingTypeName(tyname) -> string_of_type_name tyname ^ " ring"
| FieldTypeName(tyname) -> string_of_type_name tyname ^ " field"
| PolyTypeName(tyname) -> string_of_type_name tyname ^ " poly"

let rec string_of_type_expr = function
  IntExpr -> "int"
| FloatExpr -> "float"
| BoolExpr -> "bool"
| StringExpr -> "string"
| VoidExpr -> "void"
| AdtTypeExpr(adts) -> String.concat " | " (List.map (fun (name, type_name) -> if type_name == VoidName then name else name ^ " of " ^ string_of_type_name type_name) adts )
| StructTypeExpr(structs) -> "{" ^ String.concat ", " (List.map (fun (name, type_name) -> name ^ " : " ^ string_of_type_name type_name) structs ) ^ "}"
| FunType(type_expr, result) -> string_of_type_expr type_expr ^ "->" ^ string_of_type_expr result 
| PairType(type_expr1, type_expr2) -> "(" ^ string_of_type_expr type_expr1 ^ string_of_type_expr type_expr2 ^ ")"
| ListType(type_expr) -> string_of_type_expr type_expr ^ " list"
| GroupType(type_expr) -> string_of_type_expr type_expr ^ " group"
| RingType(type_expr) -> string_of_type_expr type_expr ^ " ring"
| FieldType(type_expr) -> string_of_type_expr type_expr ^ " field"
| PolyType(type_expr) -> string_of_type_expr type_expr ^ " poly"

let string_of_typ_decl (typ_name, typ_expr) =
  "type " ^ typ_name ^ " = " ^ string_of_type_expr typ_expr ^ "\n"

let string_of_bind (name, typ_name) = 
  string_of_type_name typ_name ^ " " ^ name

let rec string_of_expr = function
  Literal(lit) -> string_of_int lit
| Fliteral(str) -> str
| BoolLit(true) -> "true"
| BoolLit(false) -> "false"
| StringLit(str) -> "\"" ^ str ^ "\""
| PairExpr(expr1, expr2) -> "(" ^ string_of_expr expr1 ^ "," ^ string_of_expr expr2 ^ ")"
| ListExpr(elts) -> "[" ^ String.concat ", " (List.map (fun elt -> string_of_expr elt) elts ) ^ "]"
| Name(name) -> name
| Binop(expr1,op,expr2) -> string_of_expr expr1 ^ " "  ^ string_of_op op ^ " " ^ string_of_expr expr2
| Unop(op,expr) -> string_of_uop op ^ string_of_expr expr
| Let([], body) -> "" ^ string_of_expr body
| Let((bind,expr)::lets, body) -> "let " ^ string_of_bind bind ^ " = " ^ string_of_expr expr ^ " in\n" ^ string_of_expr (Let(lets, body))
| Function(args,body) -> "(" ^ String.concat ", " args ^ ") -> " ^ string_of_expr body 
| AdtExpr(target) -> string_of_target_concrete target
| StructInit(attribs) -> "{" ^ String.concat ", " (List.map (fun (name,expr) -> name ^ " = " ^ string_of_expr expr) attribs ) ^ "}"
| StructRef(name1, name2) -> name1 ^ "." ^ name2
| Match(namelist, patexprlist) -> "match (" ^ String.concat " " (List.map (fun (name) -> name) namelist) ^ ")" ^ " with\n  | "
                                ^ String.concat "\n  | " (List.map (fun (pattern, expr) -> string_of_pattern pattern 
                                ^ " -> " ^ string_of_expr expr) patexprlist)
| Call(expr1, expr2) -> string_of_expr expr1 ^ " " ^ string_of_expr expr2
| If(expr1,expr2,expr3) -> "if " ^ string_of_expr expr1 
                         ^ " then " ^ string_of_expr expr2 
                         ^ " else " ^ string_of_expr expr3
| Group(group) -> string_of_group group
| Ring(ring) -> string_of_ring ring
| Field(field) -> string_of_field field
| Print(expr) -> "print: " ^ string_of_expr expr

and string_of_pattern = function
  Pattern(targets) -> "(" ^ String.concat ", " (List.map string_of_target_wild targets) ^ ")"  

and string_of_target_wild = function
  TargetWildName(name) -> name
| TargetWildLiteral(expr) -> string_of_expr expr
| TargetWildApp(name,target) -> name ^ "(" ^ string_of_target_wild target ^ ")"
| CatchAll -> "_"

and string_of_target_concrete = function
  TargetConcName(name) -> name
| TargetConcExpr(expr) -> string_of_expr expr
| TargetConcApp(name, target) -> name ^ string_of_target_concrete target  

and string_of_group (name, expr1, expr2, expr3, expr4) = 
  string_of_type_name name ^ " " ^
  string_of_expr expr1 ^ " " ^
  string_of_expr expr2 ^ " " ^
  string_of_expr expr3 ^ " " ^
  string_of_expr expr4

and string_of_ring(name, expr1, expr2, expr3, expr4, expr5, expr6) = 
  string_of_group (name, expr1, expr2, expr3, expr4) ^ " " ^
  string_of_expr expr5 ^ " " ^
  string_of_expr expr6

and string_of_field(name, expr1, expr2, expr3, expr4, expr5, expr6, expr7) = 
  string_of_ring (name, expr1, expr2, expr3, expr4, expr5, expr6) ^ " " ^
  string_of_expr expr7

let string_of_program (typ_decls, expr) = 
  String.concat "" (List.map string_of_typ_decl typ_decls) ^ string_of_expr expr ^ "\n"
