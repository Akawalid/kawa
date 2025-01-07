%{

  open Lexing
  open Kawa

%}

%token <int> INT
%token <string> IDENT
%token MAIN
%token LPAR RPAR BEGIN END SEMI COMMA DOT
%token MINUS PLUS MUL DIV MOD
%token NEG EQUAL NEQ LT LE GT GE AND OR TRUE FALSE
%token VAR PROTECTED PRIVATE METHOD ATTRIBUTE CLASS EXTENDS
%token ASSIGN PRINT NEW THIS IF ELSE
%token WHILE RETURN TINT TBOOL TVOID
%token EOF


%left OR
%left AND
%left EQUAL NEQ
%left LT LE GT GE
%left PLUS MINUS
%left MUL DIV MOD
%right OPP NEG
%left DOT

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
  END 
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
|  ATTRIBUTE visibility=access_rights tho=typ id=IDENT SEMI { id, tho, visibility }
;

method_def:
| METHOD visibility=access_rights tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=list(var_decl)
  code=list(instruction)
 END 
 {
  {
    method_name = id;
    visibility = visibility;
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
| IF LPAR e=expression RPAR BEGIN
    lif=list(instruction)
  END ELSE BEGIN
    lelse=list(instruction)
  END
  { If (e, lif, lelse) }
| IF LPAR e=expression RPAR BEGIN
    lif=list(instruction)
  END
  { If2 (e, lif) }
| WHILE LPAR e=expression RPAR BEGIN li=list(instruction) END { While (e, li) }
| RETURN e=expression SEMI { Return e } 
| e=expression SEMI { Expr e }
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
| MINUS expression %prec OPP { Unop (Not, $2) }
| NEG expression { Unop (Opp, $2) }
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

access_rights:
| PRIVATE { Private }
| PROTECTED { Protected }
| { PackagePrivate }

%inline bop: (*%inline est trouvé dans la documentation page 17, il sert à linéariser bop, cela sert à bien définir les priorité dans la dérivation expression bop expression*)
| PLUS { Add }
| MINUS { Sub }
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