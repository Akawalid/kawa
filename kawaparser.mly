%{

  open Lexing
  open Kawa

%}

%token <int> INT
%token <string> IDENT
%token MAIN
%token LPAR RPAR BEGIN END SEMI COMMA 
%token SUB PLUS MUL DIV // modulo à rajouter
%token NEG EQUAL NEQ LT LE GT GE AND OR TRUE FALSE
%token ASSIGN PRINT VAR ATTRIBUTE METHOD CLASS NEW THIS IF ELSE
%token WHILE RETURN TINT TBOOL TVOID
%token EOF

%start program
%type <Kawa.program> program

%%

program:
| MAIN BEGIN main=list(instruction) END EOF
    { {classes=[]; globals=[]; main} }
;

instruction:
| PRINT LPAR e=expression RPAR SEMI { Print(e) }
;

expression:
| n=INT { Int(n) }
;
