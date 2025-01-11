%{

  open Lexing
  open Kawa

%}

%{
  (*Les fonctions suivantes servent à compacter le code et le rendre facile à lire*)

  (*fusionne une liste de listes en un seule liste contenant tous les éléments. Elle prend une liste de listes en paramètre et renvoie une liste aplatie. *)
  let flatten_list l = List.fold_left (fun acc e -> e @ acc) []  l
%}

%token <int> INT
%token <string> IDENT
%token MAIN
%token LPAR RPAR RBRACK LBRACK BEGIN END SEMI COMMA DOT
%token MINUS PLUS MUL DIV MOD
%token NEG EQUAL NEQ LT LE GT GE AND OR TRUE FALSE INSTANCEOF
%token VAR STATIC FINAL PROTECTED PRIVATE METHOD ATTRIBUTE CLASS EXTENDS
%token ASSIGN PRINT NEW THIS IF ELSE
%token WHILE RETURN TINT TBOOL TVOID
%token EOF

%left OR
%left AND
%left EQUAL NEQ
%left LT LE GT GE INSTANCEOF
%left PLUS MINUS
%left MUL DIV MOD
%right OPP NEG
%left DOT

%start program
%type <Kawa.program> program

%%

program:
| globals=list(var_decl) classes=list(class_def) MAIN BEGIN main=list(instruction) END EOF
    { {classes; globals=flatten_list globals; main} }
;

class_def:
| CLASS id=IDENT pr=parent BEGIN 
    atts=list(att_decl)
    meths=list(method_def)
  END 
  {
    let atts, s_atts =
      List.fold_left (fun (acc1, acc2) (static, e) ->
        if static then acc1, e@acc2
        else e@acc1, acc2
       ) ([], []) atts
    in

    let meths, s_meths = 
      List.fold_left (fun (acc1, acc2) (static, m) ->
        if static then acc1, m::acc2
        else m::acc1, acc2
       ) ([], []) meths
    in
    {
      class_name = id;
      attributes = atts;
      s_attributs = s_atts;
      methods = meths;
      s_methods = s_meths;
      parent = pr;
    }
  }
;

parent:
| { None }
|  EXTENDS id=IDENT { Some id }
;

att_decl_:
| id=IDENT { id, None }
| id=IDENT ASSIGN expression { id, Some $3 }

att_decl:
| ATTRIBUTE FINAL STATIC PROTECTED typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Protected, true, e) ld }
| ATTRIBUTE STATIC FINAL PROTECTED typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Protected, true, e) ld }
| ATTRIBUTE FINAL PROTECTED STATIC typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Protected, true, e) ld }
| ATTRIBUTE STATIC PROTECTED FINAL typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Protected, true, e) ld }
| ATTRIBUTE PROTECTED FINAL STATIC typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Protected, true, e) ld }
| ATTRIBUTE PROTECTED STATIC FINAL typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Protected, true, e) ld }

| ATTRIBUTE FINAL STATIC PRIVATE typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Private, true, e) ld }
| ATTRIBUTE STATIC FINAL PRIVATE typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Private, true, e) ld }
| ATTRIBUTE FINAL PRIVATE STATIC typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Private, true, e) ld }
| ATTRIBUTE STATIC PRIVATE FINAL typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Private, true, e) ld }
| ATTRIBUTE PRIVATE FINAL STATIC typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Private, true, e) ld }
| ATTRIBUTE PRIVATE STATIC FINAL typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $5, Private, true, e) ld }

| ATTRIBUTE FINAL STATIC typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $4, PackagePrivate, true, e) ld}
| ATTRIBUTE STATIC FINAL typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $4, PackagePrivate, true, e) ld}

| ATTRIBUTE STATIC typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { true, List.map (fun (id, e) -> id, $3, PackagePrivate, false, e) ld }
| ATTRIBUTE FINAL typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { false, List.map (fun (id, e) -> id, $3, PackagePrivate, true, e) ld}
| ATTRIBUTE typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI { false, List.map (fun (id, e) -> id, $2, PackagePrivate, false, e) ld}
;

access_rights:
| PRIVATE { Private }
| PROTECTED { Protected }
| { PackagePrivate }
;
method_def:
| METHOD STATIC visibility=access_rights tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=list(var_decl)
  code=list(instruction)
 END 
  {
  true, 
  {
    method_name = id;
    visibility = visibility;
    code = code;
    params = params;
    locals = flatten_list locals;
    return = tho;
  }
 }

| METHOD visibility=access_rights tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=list(var_decl)
  code=list(instruction)
 END 
 {
  false, 
  {
    method_name = id;
    visibility = visibility;
    code = code;
    params = params;
    locals = flatten_list locals;
    return = tho;
  }
 }

 
;

typ:
| typ_base { $1 }
| typ LBRACK RBRACK { TArray $1 }
;

typ_base:
| TBOOL { TBool }
| TINT { TInt }
| TVOID { TVoid }
| id=IDENT { TClass(id) }

params_nempty: 
| tho=typ id=IDENT {[id, tho]}
| params=params COMMA tho=typ id=IDENT { (id, tho)::params }
; 

params:
| { [] }
| li = params_nempty { li }
;

var_decl:
| VAR tho=typ ld=separated_nonempty_list(COMMA, att_decl_) SEMI
  {List.map (fun (id, e) -> id, tho, e) ld}
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
| n=INT LBRACK e=expression RBRACK { Tab(e, n) }

expression:
| n=INT { Int(n) }
| FALSE { Bool false }
| TRUE { Bool true }
| THIS { This }
| mem { Get $1 }
| LPAR expression RPAR { $2 }
| MINUS expression %prec OPP { Unop (Opp, $2) }
| NEG expression { Unop (Not, $2) }
| expression bop expression { Binop ($2, $1, $3) }
| NEW id=IDENT { New id }
| NEW id=IDENT LPAR args RPAR { NewCstr (id, $4) }
| expression DOT id=IDENT LPAR args RPAR { MethCall ($1, id, $5) }
| LBRACK separated_list(SEMI, expression) RBRACK { Array $2 }
| NEW typ_base d=dimensions { NewArray($2, d) }
;

dimensions:
| LBRACK e=expression RBRACK maybe_empty_dimensions { (Some e)::$4 }
;

maybe_empty_dimensions:
| { [] }
| LBRACK RBRACK empty_dimensions_or_nothing { None::$3 }
| dimensions { $1 }
;

empty_dimensions_or_nothing:
| { [] }
| LBRACK RBRACK empty_dimensions_or_nothing { None::$3 }
;

args_nempty:
| expression { [$1] }
| args_nempty COMMA expression { $3::$1 }
; 

args:
| { [] }
| args_nempty { $1 }
;

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
| INSTANCEOF { Instanceof }
;