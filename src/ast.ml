(* Abstract Syntax Tree and functions for printing it *)

type op = Add | Sub | Mult | Div | Equal | Neq | Less | Leq | Greater | Geq |
          And | Or | Mod

type uop = Neg | Not

type name = string

type type_expr = 
    IntExpr | BoolExpr | FloatExpr | VoidExpr | StringExpr
  | TypNameExpr of name
  | AdtTypeExpr of (name * type_expr) list
  | StructTypeExpr of (name * type_expr) list
  | ParamType of type_expr list
  | FunType of type_expr * type_expr
  | PairType of type_expr * type_expr
  | ListType of type_expr
  | EmptyListType
  | GroupType of type_expr
  | RingType of type_expr
  | FieldType of type_expr
  | PolyType of type_expr

type typ_decl = name * type_expr

type bind = name * type_expr

type expr =
    Literal of int
  | Fliteral of string
  | BoolLit of bool
  | StringLit of string
  | PairExpr of expr * expr
  | ConsExpr of expr * expr
  | CarExpr of expr
  | CdrExpr of expr
  | EmptyListExpr
  | Name of name
  | Binop of expr * op * expr
  | Unop of uop * expr
  | Let of (bind * expr) list * expr
  | Function of bind list * expr
  | AdtExpr of target
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
    Pattern of target list

and target = 
    TargetWildName of name
  | TargetWildLiteral of expr
  | TargetWildApp of name * target
  | CatchAll
  
and group = type_expr * expr * expr * expr * expr
and ring = type_expr * expr * expr * expr * expr * expr * expr
and field = type_expr * expr * expr * expr * expr * expr * expr * expr

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
| Mod -> "mod"


let string_of_uop = function
  Neg -> "-"
| Not -> "!"

let rec string_of_type_expr = function
  IntExpr -> "Int"
| FloatExpr -> "Float"
| BoolExpr -> "Bool"
| StringExpr -> "String"
| VoidExpr -> "Void"
| TypNameExpr(name) -> "User-Type: " ^ name
| AdtTypeExpr(adts) -> String.concat " | " (List.map (fun (name, type_expr) -> match type_expr with VoidExpr -> name | _ -> name ^ " of " ^ string_of_type_expr type_expr) adts )
| StructTypeExpr(structs) -> "{" ^ String.concat ", " (List.map (fun (name, type_expr) -> name ^ " : " ^ string_of_type_expr type_expr) structs ) ^ "}"
| ParamType(type_exprs) -> "[" ^ String.concat ", " (List.map string_of_type_expr type_exprs) ^ "]"
| FunType(type_expr, result) -> "(" ^ string_of_type_expr type_expr ^ " -> " ^ string_of_type_expr result  ^ ")"
| PairType(type_expr1, type_expr2) -> "(" ^ string_of_type_expr type_expr1 ^ " * " ^ string_of_type_expr type_expr2 ^ ")"
| ListType(type_expr) -> string_of_type_expr type_expr ^ " list"
| EmptyListType -> "[]"
| GroupType(type_expr) -> string_of_type_expr type_expr ^ " group"
| RingType(type_expr) -> string_of_type_expr type_expr ^ " ring"
| FieldType(type_expr) -> string_of_type_expr type_expr ^ " field"
| PolyType(type_expr) -> string_of_type_expr type_expr ^ " poly"

let string_of_typ_decl (typ_name, typ_expr) =
  "type " ^ typ_name ^ " = " ^ string_of_type_expr typ_expr ^ "\n"

let string_of_bind (name, typ_expr) = 
  string_of_type_expr typ_expr ^ " " ^ name

let rec string_of_expr = function
  Literal(lit) -> string_of_int lit
| Fliteral(str) -> str
| BoolLit(true) -> "true"
| BoolLit(false) -> "false"
| StringLit(str) -> "\"" ^ str ^ "\""
| PairExpr(expr1, expr2) -> "(" ^ string_of_expr expr1 ^ "," ^ string_of_expr expr2 ^ ")"
| ConsExpr(expr1, expr2) -> "(" ^ string_of_expr expr1 ^ " :: " ^ string_of_expr expr2 ^ ")"
| CarExpr(expr) -> "car " ^ string_of_expr expr
| CdrExpr(expr) -> "cdr " ^ string_of_expr expr
| EmptyListExpr -> "[]"
| Name(name) -> name
| Binop(expr1,op,expr2) -> string_of_expr expr1 ^ " "  ^ string_of_op op ^ " " ^ string_of_expr expr2
| Unop(op,expr) -> string_of_uop op ^ string_of_expr expr
| Let([], body) -> "" ^ string_of_expr body
| Let((bind,expr)::lets, body) -> "let " ^ string_of_bind bind ^ " = " ^ string_of_expr expr ^ " in\n" ^ string_of_expr (Let(lets, body))
| Function(args,body) -> "(" ^ String.concat ", " (List.map string_of_bind args) ^ ") -> " ^ string_of_expr body 
| AdtExpr(target) -> string_of_target target
| StructInit(attribs) -> "{" ^ String.concat ", " (List.map (fun (name,expr) -> name ^ " = " ^ string_of_expr expr) attribs ) ^ "}"
| StructRef(name1, name2) -> name1 ^ "." ^ name2
| Match(args, patexprlist) -> "match (" ^ String.concat ", " args ^ ")" ^ " with\n  | "
                                ^ String.concat "\n  | " (List.map (fun (pattern, expr) -> string_of_pattern pattern 
                                ^ " -> " ^ string_of_expr expr) patexprlist)
(* | Match(args, patexprlist) -> "match (" ^ String.concat " " args ^ ")" ^ " with\n  | "
                                ^ String.concat "\n  | " (List.map (fun (pattern, expr) -> string_of_pattern pattern 
                                ^ " -> " ^ string_of_expr expr) patexprlist) *)
| Call(expr1, expr2) -> "(" ^ string_of_expr expr1 ^ " " ^ string_of_expr expr2 ^ ")"
| If(expr1,expr2,expr3) -> "if " ^ string_of_expr expr1 
                         ^ " then " ^ string_of_expr expr2 
                         ^ " else " ^ string_of_expr expr3
| Group(group) -> string_of_group group
| Ring(ring) -> string_of_ring ring
| Field(field) -> string_of_field field
| Print(expr) -> "print: " ^ string_of_expr expr

and string_of_pattern = function
  Pattern(targets) -> "(" ^ String.concat ", " (List.map string_of_target targets) ^ ")"  

and string_of_target = function
  TargetWildName(name) -> name
| TargetWildLiteral(expr) -> string_of_expr expr
| TargetWildApp(name,target) -> name ^ "(" ^ string_of_target target ^ ")"
| CatchAll -> "_" 

and string_of_group (name, expr1, expr2, expr3, expr4) = 
  string_of_type_expr name ^ " " ^
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
