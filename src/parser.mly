/* Ocamlyacc parser for Grouper */

%{
open Ast
%}

%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COLON DOT COMMA PLUS MINUS STAR DIVIDE MOD ASSIGN UNDERSCORE ARROW
%token EQ NEQ LT LEQ GT GEQ AND OR NOT NEG CONS CAR CDR NULL
%token GROUP RING FIELD POLY LET IN LAND IF THEN ELSE
%token TYPE OF BAR LIST INT BOOL FLOAT STRING VOID PRINT
%token FUNCTION MATCH WITH END FUN
%token <int> LITERAL
%token <bool> BLIT
%token <string> NAME ADTNAME TYPNAME FLIT STRINGLIT
%token EOF MAX

%start program
%type <Ast.program> program

%nonassoc NOIN
%nonassoc LET IN PRINT
%nonassoc FUNCTION IF
%nonassoc COMMA
%right ARROW
%right ASSIGN
%nonassoc LITERAL FLIT BLIT STRINGLIT NAME ADTNAME
%nonassoc LPAREN RPAREN LBRACE LBRACKET RBRACE RBRACKET
%left CONS
%left OR AND
%left EQ NEQ LT GT LEQ GEQ
%left PLUS MINUS
%left STAR DIVIDE MOD
%nonassoc GROUP RING FIELD
%nonassoc POLY
%nonassoc LIST
%nonassoc FUN
%nonassoc CAR CDR NULL
%nonassoc NOT NEG
%nonassoc MAX

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
  | LPAREN type_expr RPAREN { $2 }

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
  | NAME                  { Name($1) }
  | expr PLUS expr {Binop($1, Add, $3) }
  | expr MINUS expr {Binop($1, Sub, $3) }
  | expr STAR expr {Binop($1, Mult, $3) }
  | expr DIVIDE expr {Binop ($1, Div, $3) }
  | expr EQ expr {Binop($1, Equal, $3) }
  | expr NEQ expr {Binop($1, Neq, $3)}
  | expr LT expr {Binop($1, Less, $3)}
  | expr GT expr {Binop($1, Greater, $3)}
  | expr LEQ expr {Binop($1, Leq, $3)}
  | expr GEQ expr {Binop($1, Geq, $3)}
  | expr AND expr {Binop($1, And, $3)}
  | expr OR expr {Binop($1, Or, $3)}
  | expr MOD expr {Binop($1, Mod, $3)}
  | NEG expr { Unop(Neg, $2) }
  /*| expr binop expr     { Binop($1, $2, $3) }*/
  | NOT expr              { Unop(Not, $2) } 
  | expr CONS expr        { ConsExpr ($1, $3)}
  | CAR expr              { CarExpr ($2)}
  | CDR expr              { CdrExpr ($2)}
  | NULL expr             { Unop(Null, $2) }
  | FUNCTION fn_def       { $2 }
  | IF expr THEN expr ELSE expr END
                          { If($2, $4, $6) }
  | GROUP LBRACE type_expr COMMA expr COMMA expr COMMA expr COMMA expr RBRACE
                      { Group ($3, $5, $7, $9, $11) }        
  | RING LBRACE type_expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr RBRACE
                      { Ring  ($3, $5, $7, $9, $11, $13, $15, $17) }
  | FIELD LBRACE type_expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr COMMA expr RBRACE
                      { Field ($3, $5, $7, $9, $11, $13, $15, $17) }
  | LBRACE struct_init_body RBRACE
                          { StructInit($2) }
  | NAME DOT NAME         { StructRef($1, $3) }
  | PRINT expr            { Print($2) }
  | target_conc  { AdtExpr($1) }
  | LPAREN expr RPAREN  { $2 }
  | expr expr %prec FUN { Call($1, $2) }


//-------------------- FUNCTION DEFINITION --------------------//

fn_def:
    formals expr END           { Function($1, $2)}
  // | formals MATCH formals WITH match_rule END { Function($1, Match($3, $5)) }
  | formals MATCH LPAREN var_list RPAREN WITH match_rule END { Function($1, Match($4, $7)) }
  // | formals MATCH LPAREN var_list RPAREN WITH match_rule END { Function($1, Match($4, $7)) }

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
var_list:
    NAME                 { [$1] }
  | var_list COMMA NAME  { $3 :: $1 }

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
  | ADTNAME LPAREN target_wild RPAREN %prec MAX { TargetWildApp($1, $3) }
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
      ADTNAME                { TargetWildName($1) }
    | ADTNAME LPAREN expr RPAREN %prec MAX   { TargetWildApp($1, TargetWildLiteral($3)) }


//-------------------- MISC RULES --------------------//

struct_init_body:
    NAME ASSIGN expr                         { [($1, $3)] }
  | NAME ASSIGN expr COMMA struct_init_body { ($1, $3) :: $5 }


inside_list:
    /* nothing */           { EmptyListExpr }
  | expr                    { ConsExpr ($1, EmptyListExpr) }
  | expr COMMA inside_list  { ConsExpr ($1, $3) }

/*binop:
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
  | MOD     { Mod }*/
