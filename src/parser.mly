/* Ocamlyacc parser for MicroC */

%{
open Ast
%}

%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COLON DOT COMMA PLUS MINUS STAR DIVIDE ASSIGN ARROW
%token EQ NEQ LT LEQ GT GEQ AND OR NOT
%token GROUP RING FIELD LET IN LAND IF THEN ELSE END
%token TYPE OF BAR LIST PAIR INT BOOL FLOAT STRING
%token <int> LITERAL
%token <bool> BLIT
%token <string> NAME FLIT STRINGLIT
%token EOF

%start program
%type <Ast.program> program


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
  tdecls lexpr EOF { ($1, $2) }

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
| typ STAR typ  { Pair($1, $3) }
| typ ARROW typ { FTyp($1, $3) }

utyp:
  NAME              { (Name($1), Void) }
| NAME OF typ       { (Name($1), $3) }

utyp_opt:
  utyp              { [$1] }
| utyp BAR utyp_opt { $1 :: $3 }

// ----------- progress --------------

formals_opt:
    /* nothing */ { [] }
  | formal_list   { $1 }

formal_list:
    typ ID                   { [($1,$2)]     }
  | formal_list COMMA typ ID { ($3,$4) :: $1 }



vdecl_list:
    /* nothing */    { [] }
  | vdecl_list vdecl { $2 :: $1 }

vdecl:
   typ ID SEMI { ($1, $2) }

stmt_list:
    /* nothing */  { [] }
  | stmt_list stmt { $2 :: $1 }

stmt:
    expr SEMI                               { Expr $1               }
  | RETURN expr_opt SEMI                    { Return $2             }
  | LBRACE stmt_list RBRACE                 { Block(List.rev $2)    }
  | IF LPAREN expr RPAREN stmt %prec NOELSE { If($3, $5, Block([])) }
  | IF LPAREN expr RPAREN stmt ELSE stmt    { If($3, $5, $7)        }
  | FOR LPAREN expr_opt SEMI expr SEMI expr_opt RPAREN stmt
                                            { For($3, $5, $7, $9)   }
  | WHILE LPAREN expr RPAREN stmt           { While($3, $5)         }

expr_opt:
    /* nothing */ { Noexpr }
  | expr          { $1 }

expr:
    LITERAL          { Literal($1)            }
  | FLIT	     { Fliteral($1)           }
  | BLIT             { BoolLit($1)            }
  | ID               { Id($1)                 }
  | expr PLUS   expr { Binop($1, Add,   $3)   }
  | expr MINUS  expr { Binop($1, Sub,   $3)   }
  | expr TIMES  expr { Binop($1, Mult,  $3)   }
  | expr DIVIDE expr { Binop($1, Div,   $3)   }
  | expr EQ     expr { Binop($1, Equal, $3)   }
  | expr NEQ    expr { Binop($1, Neq,   $3)   }
  | expr LT     expr { Binop($1, Less,  $3)   }
  | expr LEQ    expr { Binop($1, Leq,   $3)   }
  | expr GT     expr { Binop($1, Greater, $3) }
  | expr GEQ    expr { Binop($1, Geq,   $3)   }
  | expr AND    expr { Binop($1, And,   $3)   }
  | expr OR     expr { Binop($1, Or,    $3)   }
  | MINUS expr %prec NOT { Unop(Neg, $2)      }
  | NOT expr         { Unop(Not, $2)          }
  | ID ASSIGN expr   { Assign($1, $3)         }
  | ID LPAREN args_opt RPAREN { Call($1, $3)  }
  | LPAREN expr RPAREN { $2                   }

args_opt:
    /* nothing */ { [] }
  | args_list  { List.rev $1 }

args_list:
    expr                    { [$1] }
  | args_list COMMA expr { $3 :: $1 }
