/* Ocamlyacc parser for MicroC */

%{
open Ast
%}

%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COLON DOT COMMA PLUS MINUS STAR DIVIDE ASSIGN UNDERSCORE ARROW
%token EQ NEQ LT LEQ GT GEQ AND OR NOT
%token GROUP RING FIELD LET IN LAND IF THEN ELSE END
%token TYPE OF BAR LIST PAIR INT BOOL FLOAT STRING
%token FUNCTION MATCH WITH
%token <int> LITERAL
%token <bool> BLIT
%token <string> NAME FLIT STRINGLIT
%token EOF

%start program
%type <Ast.program> program

%nonassoc NOIN
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

tdecls:
    /* nothing */ { []       }
  | tdecls tdecl  { $2 :: $1 }

tdecl:
  TYPE NAME ASSIGN typ { ($2, $4) }

typ:
    INT           { Int   }
  | BOOL          { Bool  }
  | FLOAT         { Float }
  | STRING        { String }
  | utyp_opt      { UTyp($1) }
  | typ LIST      { List($1) }
  | typ STAR typ  { PairType($1, $3) }
  | typ ARROW typ { FTyp($1, $3) }

utyp:
    NAME              { (Name($1), Void) }
  | NAME OF typ       { (Name($1), $3) }

utyp_opt:
    utyp              { [$1] }
  | utyp BAR utyp_opt { $1 :: $3 }

lexprs:
    /* nothing */ { []       }
  | lexprs lexpr  { $2 :: $1 }

lexpr:
    LET letand_opt %prec NOIN 
  | LET letand_opt IN expr

letand_opt:
    typ_name NAME ASSIGN expr              {}
  | typ_name NAME ASSIGN expr LAND letand  {}

typ_name:
    NAME
  | typ

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
  | IF expr THEN expr ELSE expr END
                          { If($2, $4, $6) }

list_expr
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

fn_def:
    formals expr                     { Function($1, $2)}
  | formals MATCH formals WITH match { Function($1, Match($3, $5)) }

match:
    match_line { [$1] }
  | match_line match { $1 :: $2 }

match_line:
  BAR pattern ARROW expr { (Pattern($2), $4) }

pattern:
    target                    { [$1]) }
  | LPAREN target_list RPAREN { $2 }

target_list:
    target              { [$1] }
  | target target_list  { $1 :: $3}

target:
    NAME                      { TargetName($1) }
  | expr                      { TargetExpr($1) }
  | NAME LPAREN target RPAREN { TargetApp($1, $3) }
  | UNDERSCORE                { CatchAll }

formals:
  LPAREN formals_opt RPAREN { $2 }

formals_opt:
    /* nothing */ { [] }
  | formal_list   { $1 }

formal_list:
    NAME              { [$1] }
  | formal_list NAME  { $2 :: $1 }
