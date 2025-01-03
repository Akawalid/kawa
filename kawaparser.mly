%{

  open Lexing
  open Kawa

%}

%token <int> INT
%token <string> IDENT
%token MAIN
%token LPAR RPAR BEGIN END SEMI COMMA DOT
%token SUB PLUS MUL DIV MOD
%token NEG OPP EQUAL NEQ LT LE GT GE AND OR TRUE FALSE
%token ASSIGN PRINT VAR ATTRIBUTE METHOD CLASS EXTENDS NEW THIS IF ELSE
%token WHILE RETURN TINT TBOOL TVOID
%token EOF


// %nonassoc FALSE TRUE THIS INT RPAR IDENT 
%left PLUS SUB
%left MUL DIV
%nonassoc OPP
%nonassoc LT GT

%start program
%type <Kawa.program> program

%%

program:
| globals=list(var_decl) classes=list(class_def) MAIN BEGIN main=list(instruction) END EOF
    { {classes; globals; main} }
;

class_def:
| CLASS id=IDENT pr=parent BEGIN 
    atts=list(att_decl)
    meths=list(method_def)
  END SEMI
  {
    {
      class_name = id;
      attributes = atts;
      methods = meths;
      parent = pr;
    }
  }
;

parent:
| { None }
|  EXTENDS id=IDENT { Some id }
;

att_decl:
|  ATTRIBUTE tho=typ id=IDENT SEMI { id, tho }
;

method_def:
| METHOD tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=list(var_decl)
  code=list(instruction)
 END SEMI
 {
  {
    method_name = id;
    code = code;
    params = params;
    locals = locals;
    return = tho;
  }
 }
;

typ:
| TBOOL { TBool }
| TVOID { TVoid }
| TINT { TInt }
| id=IDENT { TClass(id) }
;

params_nempty:
| tho=typ id=IDENT {[id, tho]}
| params=params COMMA tho=typ id=IDENT { (id, tho)::params }
; 

params:
| { [] }
| li = params_nempty { li }
;

var_decl:
| VAR tho=typ id=IDENT SEMI
  {id, tho}
;

instruction:
| PRINT LPAR e=expression RPAR SEMI { Print (e) }
| v=mem ASSIGN e=expression SEMI { Set (v, e) }
| IF e=expression BEGIN
    lif=list(instruction)
  END ELSE BEGIN
    lelse=list(instruction)
  END
  { If (e, lif, lelse) }
| WHILE e=expression BEGIN li=list(instruction) END { While (e, li) }
| RETURN e=expression SEMI { Return e } 
| e=expression { Expr e }
;

mem:
| id=IDENT { Var(id) }
| e=expression DOT id=IDENT { Field(e, id) }

expression:
| n=INT { Int(n) }
| FALSE { Bool false }
| TRUE { Bool true }
| THIS { This }
| mem { Get $1 }
| LPAR expression RPAR { $2 }
| uop expression { Unop ($1, $2) }
| expression bop expression { Binop ($2, $1, $3) }
| NEW id=IDENT { New id }
| NEW id=IDENT LPAR args RPAR { NewCstr (id, $4) }
| expression DOT id=IDENT LPAR args RPAR { MethCall ($1, id, $5) }
;

args_nempty:
| expression { [$1] }
| args_nempty COMMA expression { $3::$1 }
; 

args:
| { [] }
| args_nempty { $1 }
;

uop:
| NEG { Not }
| OPP { Opp }
;

bop:
| PLUS { Add }
| SUB { Sub }
| MUL { Mul}
| DIV { Div }
| MOD { Rem } 
| LT { Lt } 
| LE { Le }
| GT { Gt }
| GE { Ge }
| EQUAL { Eq }
| NEQ { Neq }
| AND { And }
| OR {Or}
;