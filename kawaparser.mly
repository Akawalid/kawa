%{

  open Lexing
  open Kawa

%}

%{
  (*Les déclarations suivantes servent à compacter le code et le rendre facile à lire*)

  (* Ce type sert à parser les méthodes dans une liste pour les traiter dans la règle class_def. *)
  type method_type = 
  Abstract of abstract_method_def
  | Concret of bool * method_def (*Bool pour savoir si c'est une méthode statique ou pas*)
  
  let create_meth_object is_static id visibility code params locals tho = 
  Concret(is_static, 
  {
    method_name = id;
    visibility = visibility;
    code = code;
    params = params;
    locals = locals;
    return = tho;
  }
  )

  let create_abs_meth_object id visibility params tho = 
  Abstract ({
    abs_method_name = id;
    abs_visibility = visibility;
    abs_params = params;
    abs_return = tho;
  })

%}

%token <int> INT
%token <string> IDENT
%token MAIN
%token LPAR RPAR RBRACK LBRACK BEGIN END SEMI COMMA DOT
%token MINUS PLUS MUL DIV MOD
%token NEG EQUAL NEQ LT LE GT GE AND OR TRUE FALSE INSTANCEOF
%token STATIC FINAL PROTECTED PRIVATE CLASS EXTENDS ABSTRACT
%token ASSIGN PRINT NEW THIS IF ELSE
%token WHILE RETURN TINT TBOOL TVOID
%token EOF NULL

%nonassoc TVOID
%nonassoc REDUCE_PREFERENCE
%nonassoc TINT TBOOL STATIC PROTECTED PRIVATE IDENT

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
| globals=var_decl_l classes=list(class_def) MAIN BEGIN main=list(instruction) END EOF
    { {classes; globals=List.flatten globals; main} }
;

parent:
| { None }
|  EXTENDS id=IDENT { Some id }
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

params_nempty: 
| tho=typ id=IDENT {[id, tho]}
| params=params COMMA tho=typ id=IDENT { (id, tho)::params }
; 

params:
| { [] }
| li = params_nempty { li }
;

abs_method_params_nempty: 
| tho=typ id=IDENT {[tho]}
| params=abs_method_params_nempty COMMA tho=typ IDENT { tho::params }
; 

abs_method_params:
| { [] }
| li = abs_method_params_nempty { li }
;

var_decl:
| tho=typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI
  {List.map (fun (id, e) -> id, tho, e) ld}
;

var_decl_l:
| %prec REDUCE_PREFERENCE { [] }
| var_decl var_decl_l { $1 :: $2 }
;

ident_and_maybe_initialisation:
| id=IDENT { id, None }
| id=IDENT ASSIGN expression { id, Some $3 }
;

(*
  La liste des regles est trop longue parceque j'ai traité toutes les permutations
  possibles des symbolesde droits d'acces, static, final.
*)

att_decl:
| STATIC FINAL PROTECTED typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Protected, true, e) ld }
| FINAL STATIC PROTECTED typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Protected, true, e) ld }
| FINAL PROTECTED STATIC typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Protected, true, e) ld }
| PROTECTED FINAL STATIC typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Protected, true, e) ld }
| STATIC PROTECTED FINAL typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Protected, true, e) ld }
| PROTECTED STATIC FINAL typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Protected, true, e) ld }

| FINAL STATIC PRIVATE typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Private, true, e) ld }
| STATIC FINAL PRIVATE typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Private, true, e) ld }
| FINAL PRIVATE STATIC typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Private, true, e) ld }
| STATIC PRIVATE FINAL typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Private, true, e) ld }
| PRIVATE FINAL STATIC typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Private, true, e) ld }
| PRIVATE STATIC FINAL typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $4, Private, true, e) ld }

| FINAL STATIC typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $3, PackagePrivate, true, e) ld}
| STATIC FINAL typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $3, PackagePrivate, true, e) ld}

| FINAL PRIVATE typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { false, List.map (fun (id, e) -> id, $3, Private, true, e) ld}
| PRIVATE FINAL typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { false, List.map (fun (id, e) -> id, $3, Private, true, e) ld}

| FINAL PROTECTED typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { false, List.map (fun (id, e) -> id, $3, Protected, true, e) ld}
| PROTECTED FINAL typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { false, List.map (fun (id, e) -> id, $3, Protected, true, e) ld}

| PRIVATE STATIC typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $3, Private, false, e) ld}
| STATIC PRIVATE typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $3, Private, false, e) ld}

| PROTECTED STATIC typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $3, Protected, false, e) ld}
| STATIC PROTECTED typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $3, Protected, false, e) ld}

| STATIC typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { true, List.map (fun (id, e) -> id, $2, PackagePrivate, false, e) ld }
| FINAL typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { false, List.map (fun (id, e) -> id, $2, PackagePrivate, true, e) ld}
| PRIVATE typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { false, List.map (fun (id, e) -> id, $2, Private, false, e) ld }
| PROTECTED typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { false, List.map (fun (id, e) -> id, $2, Protected, false, e) ld}

| typ ld=separated_nonempty_list(COMMA, ident_and_maybe_initialisation) SEMI { false, List.map (fun (id, e) -> id, $1, PackagePrivate, false, e) ld}

l_att_decl:
|  %prec REDUCE_PREFERENCE { [] }
| att_decl l_att_decl { $1 :: $2 }
;

method_def:
| STATIC PRIVATE tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=var_decl_l
  code=list(instruction)
 END { create_meth_object true id Private code params (List.flatten locals) tho }

| STATIC PROTECTED tho=typ id=IDENT LPAR params=params RPAR BEGIN
locals=var_decl_l
code=list(instruction)
END { create_meth_object true id Protected code params (List.flatten locals) tho }

| PRIVATE STATIC tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=var_decl_l
  code=list(instruction)
 END { create_meth_object true id Private code params (List.flatten locals) tho }

| PROTECTED STATIC tho=typ id=IDENT LPAR params=params RPAR BEGIN
locals=var_decl_l
code=list(instruction)
END { create_meth_object true id Protected code params (List.flatten locals) tho }

| STATIC tho=typ id=IDENT LPAR params=params RPAR BEGIN
locals=var_decl_l
code=list(instruction)
END { create_meth_object true id PackagePrivate code params (List.flatten locals) tho }

| PRIVATE tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=var_decl_l
  code=list(instruction)
 END { create_meth_object false id Private code params (List.flatten locals) tho}

| PROTECTED tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=var_decl_l
  code=list(instruction)
 END { create_meth_object false id Protected code params (List.flatten locals) tho}

| tho=typ id=IDENT LPAR params=params RPAR BEGIN
  locals=var_decl_l
  code=list(instruction)
 END { create_meth_object false id PackagePrivate code params (List.flatten locals) tho}

  
| ABSTRACT PROTECTED tho=typ id=IDENT LPAR params=abs_method_params RPAR SEMI
 { create_abs_meth_object id Protected params tho}
 
| ABSTRACT tho=typ id=IDENT LPAR params=abs_method_params RPAR SEMI 
{ create_abs_meth_object id PackagePrivate params tho}
 
| PROTECTED ABSTRACT tho=typ id=IDENT LPAR params=abs_method_params RPAR SEMI
 { create_abs_meth_object id Protected params tho}
;

class_def:
| abstract=option(ABSTRACT) CLASS id=IDENT pr=parent BEGIN 
    atts=l_att_decl
    meths=list(method_def)
  END 
  {
    let atts, s_atts =
      List.fold_left (fun (acc1, acc2) (static, e) ->
        if static then acc1, e@acc2
        else e@acc1, acc2
       ) ([], []) atts
    in

    let meths, s_meths, abs_meths = 
      List.fold_left (fun (acc1, acc2, acc3) e ->
        match e with 
        Concret(static, m) ->
          if static then acc1, m::acc2, acc3
          else m::acc1, acc2, acc3
        | Abstract m ->  acc1, acc2, m::acc3
       ) ([], [], []) meths
    in
    {
      class_name = id;
      is_abstract = abstract <> None;
      attributes = atts;
      s_attributs = s_atts;
      methods = meths;
      s_methods = s_meths;
      abstract_methods = abs_meths;
      parent = pr;
    }
  }
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
| NULL { NullPtr }
| FALSE { Bool false }
| TRUE { Bool true }
| THIS { This }
| mem { Get $1 }
| LPAR expression RPAR { $2 }
| MINUS expression %prec OPP { Unop (Opp, $2) }
| NEG expression { Unop (Not, $2) }
| expression bop expression { Binop ($2, $1, $3) }
| NEW id=IDENT { New id }
| NEW id=IDENT LPAR separated_list(COMMA, expression) RPAR { NewCstr (id, $4) }
| expression DOT id=IDENT LPAR separated_list(COMMA, expression) RPAR { MethCall ($1, id, $5) }
| LBRACK separated_list(SEMI, expression) RBRACK { Array $2 }
| NEW typ_base d=dimensions { NewArray($2, d) }
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