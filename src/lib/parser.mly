// parser.mly

%{
  open Absyn
%}

%token                 EOF
%token <bool>          LITBOOL
%token <int>           LITINT
%token <float>         LITREAL
%token <Symbol.symbol> ID

%token                 PLUS
%token                 MINUS
%token                 TIMES
%token                 DIV
%token                 MOD
%token                 POW
%token                 EQ
%token                 NE
%token                 GT
%token                 GE
%token                 LT
%token                 LE
%token                 AND
%token                 OR
%token                 ASSIGN
%token                 LPAREN
%token                 RPAREN
%token                 COMMA
%token                 SEMI
%token                 COLON
%token                 BREAK
%token                 DO
%token                 ELSE
%token                 END
%token                 IF
%token                 IN
%token                 LET
%token                 THEN
%token                 VAR
%token                 WHILE

%start <Absyn.lexp> program

%%

program:
| e=exp EOF            {e}

exp:
| x=LITBOOL            {$loc, BoolExp x}
| x=LITINT             {$loc, IntExp x}
| x=LITREAL            {$loc, RealExp x}
| MINUS e=exp          {$loc, NegativeExp e}
| l=exp PLUS r=exp     {$loc, BinaryExp (l, Plus, r)}
| l=exp MINUS r=exp    {$loc, BinaryExp (l, Minus, r)}
| l=exp TIMES r=exp    {$loc, BinaryExp (l, Times, r)}
| l=exp DIV r=exp      {$loc, BinaryExp (l, Div, r)}
| l=exp MOD r=exp      {$loc, BinaryExp (l, Mod, r)}
| l=exp POW r=exp      {$loc, BinaryExp (l, Power, r)}
| WHILE t=exp DO b=exp {$loc, WhileExp (t, b)}
| BREAK                {$loc, BreakExp}
