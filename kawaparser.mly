%{

  open Lexing
  open Kawa

%}

%token <int> INT
%token <string> IDENT
%token MAIN
%token LPAR RPAR BEGIN END SEMI COMMA DOT
%token SUB PLUS MUL DIV // modulo à rajouter
%token NEG EQUAL NEQ LT LE GT GE AND OR TRUE FALSE
%token ASSIGN PRINT VAR ATTRIBUTE METHOD CLASS NEW THIS IF ELSE
%token WHILE RETURN TINT TBOOL TVOID
%token EOF

%start program
%type <Kawa.program> program

%%

program:
| glbs=var_decl classes=class_def MAIN BEGIN main=seq_instr END EOF
    { {classes=classes; globals=glbs; main} }
;

class_def:
| CLASS id=IDENT BEGIN atts=attr_decl mths=method_def END cd=class_def { {class_name=id; 
                                                                          attributes=atts; 
                                                                          methods=mths; 
                                                                          parent=None }::cd  }
|                                                                      { [] }


var_decl:
| VAR t=types id=IDENT SEMI vd=var_decl  { (id,t)::vd }   
|                                        { [] }

attr_decl:
| ATTRIBUTE t=types id=IDENT SEMI ad=attr_decl  { (id,t)::ad }   
|                                               { [] }

method_def:
| METHOD t=types id=IDENT LPAR ps=params RPAR 
                          BEGIN vd=var_decl s=seq_instr END mths=method_def {{
                                                                method_name= id;
                                                                code= s;
                                                                params= ps;
                                                                locals= vd;
                                                                return= t;
                                                              }::mths }
|                                                             { [] }

params:
| t=types id=IDENT COMMA p=params { (id,t)::p }
| t=types id=IDENT                { [(id,t)] }
|                                 { [] }


types:
|TVOID                       { TVoid }
|TINT                        { TInt }
|TBOOL                       { TBool }
|id=IDENT                    { TClass id }

instruction:
|PRINT LPAR e=expression RPAR SEMI                    { Print(e) }
|mem_acc=mem ASSIGN e=expression SEMI                 { Set (mem_acc, e) }
|IF LPAR e=expression RPAR BEGIN s1=seq_instr END 
                      ELSE BEGIN s2=seq_instr END     { If(e, s1, s2) }
|WHILE LPAR e=expression RPAR BEGIN s=seq_instr END   { While(e, s) }
|RETURN e=expression SEMI                             { Return(e) }
|e=expression SEMI                                    { Expr(e) }
;

seq_instr:
|i=instruction s=seq_instr  { i::s }
|                           { [] }
mem:  
|id=IDENT                   { Var(id) }
|e=expression DOT id=IDENT  { Field(e, id) }

expression:
| n=INT                                           { Int(n) }
| m=mem                                           { Get(m) }
| THIS                                            { This }
| NEW id=IDENT                                    { New(id) }
| NEW id=IDENT LPAR se=seq_expr RPAR              { NewCstr(id, se) }
| e=expression DOT id=IDENT LPAR se=seq_expr RPAR { MethCall(e, id, se)}

seq_expr:
| e=expression COMMA se=seq_expr { e::se }
| e=expression                   { [e] }
;
