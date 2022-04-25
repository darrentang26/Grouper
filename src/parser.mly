/* Ocamlyacc parser for MicroC */

%{
open Ast
%}

%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COLON DOT COMMA PLUS MINUS STAR DIVIDE MOD ASSIGN UNDERSCORE ARROW
%token EQ NEQ LT LEQ GT GEQ AND OR NOT CONS
%token GROUP RING FIELD POLY LET IN LAND IF THEN ELSE
%token TYPE OF BAR LIST INT BOOL FLOAT STRING VOID PRINT
%token FUNCTION MATCH WITH END
%token <int> LITERAL
%token <bool> BLIT
%token <string> NAME ADTNAME TYPNAME FLIT STRINGLIT
%token EOF

%start program
%type <Ast.program> program

%nonassoc NOIN
%nonassoc LET IN PRINT
%nonassoc FUNCTION IF
%right ARROW
%nonassoc LIST
%nonassoc GROUP RING FIELD POLY
%nonassoc LITERAL FLIT BLIT STRINGLIT NAME ADTNAME
%right ASSIGN
%left CONS
%left OR
%left AND
%left EQ NEQ
%left LT GT LEQ GEQ
%left PLUS MINUS
%left STAR DIVIDE MOD
%right NOT
%nonassoc COMMA
%nonassoc LBRACE LPAREN LBRACKET RPAREN RBRACE RBRACKET

%%

program:
  tdecls lexprs EOF { ($1, $2) }


//-------------------- TYPES --------------------//

tdecls:
    /* nothing */ { []       }
  | tdecls tdecl  { $2 :: $1 }

tdecl:
  TYPE TYPNAME ASSIGN type_expr { ($2, $4) }

type_expr:
    INT             { IntExpr }
  | BOOL            { BoolExpr }
  | FLOAT           { FloatExpr }
  | STRING          { StringExpr }
  | TYPNAME         { TypNameExpr($1) }
  | adt_opt         { AdtTypeExpr($1) }
  | LBRACE struct_decl_body RBRACE
                    { StructTypeExpr($2) }
  | type_expr LIST  { ListType($1) }
  | type_expr STAR type_expr
                    { PairType($1, $3) }
  | param_type_expr { ParamType($1) }
  | type_expr ARROW type_expr
                    { FunType($1, $3) }
  | type_expr GROUP { GroupType($1) }
  | type_expr RING  { RingType($1) }
  | type_expr FIELD { FieldType($1) }
  | type_expr POLY  { PolyType($1) }
  | LPAREN type_expr RPAREN
                    { $2 }

adt_opt:
    adt_type_expr             { [$1] }
  | adt_type_expr BAR adt_opt { $1 :: $3 }

adt_type_expr:
    ADTNAME                                     { ($1, VoidExpr) }
  | ADTNAME OF LPAREN type_expr RPAREN %prec IN { ($1, $4) }

struct_decl_body:
    NAME COLON type_expr                        { [($1, $3)] }
  | NAME COLON type_expr COMMA struct_decl_body { ($1, $3) :: $5 }

param_type_expr:
    LBRACKET type_expr_list RBRACKET            { $2 }

type_expr_list:
    type_expr                                   { [$1] }
  | type_expr COMMA type_expr_list              { $1 :: $3 }

//-------------------- LET AND EXPRESSIONS --------------------//

lexprs:
    LET letand_opt lexprs { Let($2, $3) }
  | lexpr                 { $1 }

lexpr:
  LET letand_opt IN expr  { Let($2, $4) }

letand_opt:
    type_expr NAME ASSIGN expr                  { [(($2, $1), $4)] }
  | type_expr NAME ASSIGN expr LAND letand_opt  { (($2, $1), $4) :: $6 }
    
expr:
    lexpr                 { $1 }
  | LITERAL          { Literal($1) }
  | FLIT	                { Fliteral($1) }
  | BLIT                  { BoolLit($1) }
  | STRINGLIT             { StringLit($1) }
  | LPAREN expr COMMA expr RPAREN
                          { PairExpr($2, $4) }
  | LBRACKET inside_list RBRACKET  { $2 }
  | expr CONS expr        { ConsExpr ($1, $3)}
  | NAME                  { Name($1) }
  | expr binop expr %prec STAR { Binop($1, $2, $3) }
  | MINUS expr %prec NOT  { Unop(Neg, $2) }
  | NOT expr              { Unop(Not, $2) } 
  | FUNCTION fn_def       { $2 }
  | expr expr   %prec NOT { Call($1, $2) }
  | IF expr THEN expr ELSE expr END
                          { If($2, $4, $6) }
  | GROUP LBRACE type_expr COMMA expr COMMA expr COMMA expr COMMA expr RBRACE
                      { Group ($3, $5, $7, $9, $11) }        
  | RING LBRACE type_expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr RBRACE
                      { Ring  ($3, $5, $7, $9, $11, $13, $15) }
  | FIELD LBRACE type_expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr RBRACE
                      { Field ($3, $5, $7, $9, $11, $13, $15, $17) }
  | LBRACE struct_init_body RBRACE
                          { StructInit($2) }
  | NAME DOT NAME         { StructRef($1, $3) }
  | PRINT expr            { Print($2) }
  | target_conc %prec IN          { AdtExpr($1) }
  | LPAREN expr RPAREN    { $2 }


//-------------------- FUNCTION DEFINITION --------------------//

fn_def:
    formals expr END           { Function($1, $2)}
  | formals MATCH formals WITH match_rule END { Function($1, Match($3, $5)) }

//---------- formals ----------//
formals:
  LPAREN formals_opt RPAREN { List.rev $2 }

formals_opt:
    /* nothing */ { [] }
  | formal_list   { $1 }

formal_list:
    type_expr NAME              { [($2, $1)] }
  | formal_list type_expr NAME  { ($3, $2) :: $1 }

//---------- pattern matching ----------//
match_rule:
    match_line { [$1] }
  | match_line match_rule { $1 :: $2 }

match_line:
  BAR LPAREN pattern RPAREN ARROW expr { (Pattern($3), $6) }

pattern:
    target_wild  { [$1] }
  | target_wild COMMA pattern { $1 :: $3 }

target_wild:
    ADTNAME                           { TargetWildName($1) }
  | literal                           { TargetWildLiteral($1) }
  | ADTNAME LPAREN target_wild RPAREN { TargetWildApp($1, $3) }
  | UNDERSCORE                        { CatchAll }

literal:
    LITERAL               { Literal($1) }
  | FLIT	                { Fliteral($1) }
  | BLIT                  { BoolLit($1) }
  | STRINGLIT             { StringLit($1) }
  | NAME                  { Name($1) }
  | LPAREN literal COMMA literal RPAREN
                          { PairExpr($2, $4) }

target_conc:
      ADTNAME                           { TargetWildName($1) }
    | ADTNAME LPAREN expr RPAREN        { TargetWildApp($1, TargetWildLiteral($3)) }


//-------------------- MISC RULES --------------------//

struct_init_body:
    NAME ASSIGN expr                         { [($1, $3)] }
  | NAME ASSIGN expr COMMA struct_init_body { ($1, $3) :: $5 }


inside_list:
    /* nothing */           { EmptyListExpr }
  | expr                    { ConsExpr ($1, EmptyListExpr) }
  | expr COMMA inside_list  { ConsExpr ($1, $3) }

binop:
    PLUS    { Add }
  | MINUS   { Sub }
  | STAR    { Mult }
  | DIVIDE  { Div }
  | EQ      { Equal }
  | NEQ     { Neq }
  | LT      { Less }
  | GT      { Greater}
  | LEQ     { Leq }
  | GEQ     { Geq }
  | AND     { And}
  | OR      { Or }
  | MOD     { Mod }
