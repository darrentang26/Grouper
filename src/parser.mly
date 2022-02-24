/* Ocamlyacc parser for MicroC */

%{
open Ast
%}

%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COLON DOT COMMA PLUS MINUS STAR DIVIDE ASSIGN UNDERSCORE ARROW
%token EQ NEQ LT LEQ GT GEQ AND OR NOT
%token GROUP RING FIELD POLY LET IN LAND IF THEN ELSE
%token TYPE OF BAR LIST INT BOOL FLOAT STRING VOID PRINT
%token FUNCTION MATCH WITH
%token <int> LITERAL
%token <bool> BLIT
%token <string> NAME ADTNAME FLIT STRINGLIT
%token EOF

%start program
%type <Ast.program> program

%nonassoc IN
%right ASSIGN
%left ARROW
%left OR
%left AND
%left EQ NEQ
%left LT GT LEQ GEQ
%left PLUS MINUS
%left STAR DIVIDE
%right NOT

%%

program:
  tdecls lexprs EOF { ($1, $2) }


//-------------------- TYPES --------------------//

tdecls:
    /* nothing */ { []       }
  | tdecls tdecl  { $2 :: $1 }

tdecl:
  TYPE NAME ASSIGN type_expr { ($2, $4) }

type_expr:
    INT             { IntExpr }
  | BOOL            { BoolExpr }
  | FLOAT           { FloatExpr }
  | STRING          { StringExpr }
  | VOID            { VoidExpr }
  | adt_opt         { AdtTypeExpr($1) }
  | LBRACE struct_decl_body RBRACE
                    { StructTypeExpr($2) }
  | type_expr LIST  { ListType($1) }
  | type_expr STAR type_expr
                    { PairType($1, $3) }
  | type_expr ARROW type_expr
                    { FunType($1, $3) }
  | type_expr GROUP { GroupType($1) }
  | type_expr RING  { RingType($1) }
  | type_expr FIELD { FieldType($1) }
  | type_expr POLY  { PolyType($1) }
  | LPAREN type_expr RPAREN
                    { $2 }

adt_opt:
    adt_type_expr                   { [$1] }
  | adt_type_expr BAR adt_type_expr { $1 :: $3 }

adt_type_expr:
    NAME              { (Name($1), VoidName) }
  | NAME OF type_name { (Name($1), $3) }

struct_decl_body:
    NAME COLON type_name                        { [($1, $3)] }
  | NAME COLON type_name COMMA struct_decl_body { ($1, $3) :: $5 }

type_name:
    INT           { IntName   }
  | BOOL          { BoolName  }
  | FLOAT         { FloatName }
  | STRING        { StringName }
  | NAME          { UserTypeName($1) } // for adts and structs
  | type_name LIST      { ListTypeName($1) }
  | type_name STAR type_name  { PairTypeName($1, $3) }
  | type_name ARROW type_name { FunTypeName($1, $3) }
  | type_name GROUP     { GroupTypeName($1) }
  | type_name RING      { RingTypeName($1) }
  | type_name FIELD     { FieldTypeName($1) }
  | type_name POLY      { PolyTypeName($1) }


//-------------------- LET AND EXPRESSIONS --------------------//

lexprs:
    LET letand_opt lexprs { Let($2, $3) }
  | lexpr                 { $1 }

lexpr:
  LET letand_opt IN expr  { Let($2, $4) }

letand_opt:
    type_name NAME ASSIGN expr                  { [(($2, $1), $4)] }
  | type_name NAME ASSIGN expr LAND letand_opt  { (($2, $1), $4) :: $6 }
    
expr:
    lexpr                 { $1 }
  | LITERAL               { Literal($1) }
  | FLIT	                { Fliteral($1) }
  | BLIT                  { BoolLit($1) }
  | STRINGLIT             { StringLit($1) }
  | LPAREN expr COMMA expr RPAREN
                          { PairExpr($2, $4) }
  | list_expr             { ListExpr($1) }
  | NAME                  { Name($1) }
  | expr binop expr       { Binop($1, $2, $3) }
  | MINUS expr %prec NOT  { Unop(Neg, $2) }
  | NOT expr              { Unop(Not, $2) } 
  | FUNCTION fn_def       { $2 }
  | expr expr             { Call($1, $2) }
  | IF expr THEN expr ELSE expr
                          { If($2, $4, $6) }
  | algebraic_expr        { $1 }  
  | LBRACE struct_init_body RBRACE
                          { StructInit($2) }
  | NAME DOT NAME         { StructRef($1, $3) }
  | PRINT expr            { Print($2) }
  | target_conc_outer     { AdtExpr($1) }
  | LPAREN expr RPAREN    { $2 }


//-------------------- FUNCTION DEFINITION --------------------//

fn_def:
    formals expr                     { Function($1, $2)}
  | formals MATCH formals WITH match_rule { Function($1, Match($3, $5)) }

//---------- formals ----------//
formals:
  LPAREN formals_opt RPAREN { $2 }

formals_opt:
    /* nothing */ { [] }
  | formal_list   { $1 }

formal_list:
    NAME              { [$1] }
  | formal_list NAME  { $2 :: $1 }

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
  | expr                              { TargetWildExpr($1) }
  | ADTNAME LPAREN target_wild RPAREN { TargetWildApp($1, $3) }
  | UNDERSCORE                        { CatchAll }

target_conc_outer:
    ADTNAME                                 { TargetConcName($1) }
  | ADTNAME LPAREN target_conc_inner RPAREN { TargetConcApp($1, $3) }

target_conc_inner:
    target_conc_outer           { $1 }
  | ADTNAME LPAREN expr RPAREN  { TargetConcApp($1, TargetConcExpr($3)) }


//-------------------- MISC RULES --------------------//

algebraic_expr:
    GROUP type_name expr expr expr expr
                      { Group ($2, $3, $4, $5, $6) }        
  | RING type_name expr expr expr expr expr expr
                      { Ring  (Group ($2, $3, $4, $5, $6), $7, $8) }
  | FIELD type_name expr expr expr expr expr expr expr
                      { Field (Ring  (Group ($2, $3, $4, $5, $6), $7, $8), $9) }

struct_init_body:
    NAME ASSIGN expr                         { [($1, $3)] }
  | NAME ASSIGN expr COMMA struct_init_body { ($1, $3) :: $5 }

list_expr:
  | LBRACKET inside_list RBRACKET  { $2 }

inside_list:
    /* nothing */ { [] }
  | expr inside_list { $1 :: $2 }

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
