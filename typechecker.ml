open Kawa

exception Error of string
let error s = raise (Error s)
let type_error ty_actual ty_expected =
  error (Printf.sprintf "expected %s, got %s"
           (typ_to_string ty_expected) (typ_to_string ty_actual))

module Env = Map.Make(String)
type tenv = typ Env.t

let add_env l tenv =
  List.fold_left (fun env (x, t) -> Env.add x t env) tenv l

let add_class_env l env = 
  List.fold_left (fun env class_def -> 
    if(Env.mem class_def.class_name env) then error "Deux classes avec le même nom"
    else
      Env.add class_def.class_name (TClass class_def.class_name) env
    ) env l
(**)
let get_class (l: class_def list) (class_name:string): class_def = 
  try 
    List.find (fun class_d -> class_d.class_name = class_name) l
  with 
    |Not_found -> error "définition de classes non présente dans l'environement"

(* Vérifie que la liste des expressions el s'évalue de manière compatible avec le type demandé des parametres*)
let for_all_params (el:expr list) (params_types: (string * typ) list) (type_expr:expr -> typ Env.t -> typ) (tenv:typ Env.t) : unit = 
  (* les tvoid c'est juste pour intialiser *)
  let t_exepec = ref TVoid in
  let t_act = ref TVoid in
  if not( List.for_all2 (fun e (_,t) ->
      let t' = type_expr e tenv in
      t_act := t';
      t_exepec := t;
      t' = t
    ) el params_types ) then type_error !t_act !t_exepec



let typecheck_prog p =
  let tenv = add_env p.globals Env.empty in
  (* pour garder dans this la classe de l'objet courant*)
  let obj_courant = ref (TClass "this") in

  let rec check e typ tenv =
    let typ_e = type_expr e tenv in
    if typ_e <> typ then type_error typ_e typ

  and type_expr e tenv = match e with
    | Int _  -> TInt
    | Get mem_acc -> type_mem_access mem_acc tenv
    | This ->
        (match (!obj_courant) with 
        TClass "this" -> error "Utilisation de this hors classe"
        |_ -> !obj_courant)
    |New cn -> 
      (try
        Env.find cn tenv
      with
        |Not_found -> error "Classe inexistante"
      )
    (* le constructeur doit exister*)
    | NewCstr (s, el) ->
      let c = get_class p.classes s in
      (* La premiere methode déclarée doit être le constructeur*) 
      let meth = (match c.methods with 
                  |m::_-> 
                    (if (m.method_name = "constructor") then m
                    else
                      error "Pas de constructeur (ou pas déclaré en premier)")
                  |[] -> error "Il faut au moins le constructeur "
                  ) in
      if(meth.return <> TVoid) then error "Le constructeur doit avoir void comme type de retour"
      else
        for_all_params el (meth.params) type_expr tenv;
        TClass s
    
    | MethCall(e,s,el) ->
      (match(type_expr e tenv) with
        |TClass classe_name -> 
          (try 
            let meth = List.find (fun m -> m.method_name=s) (get_class p.classes classe_name).methods in
            for_all_params el (meth.params) type_expr tenv;
            meth.return
          with
          |Not_found-> error "Méthode inexistante"
          )
        |_ -> error "Appel de méthode se fait que sur des objets"
      )

    | _ -> failwith "case not implemented in type_expr"

  and type_mem_access m tenv = match m with
    | Var s -> 
      (try
        Env.find s tenv
      with
        |Not_found -> error "variable inexistante"
      )
    |Field(e, s) ->
      (match (type_expr e tenv) with
        TClass class_name -> 
          let c = get_class p.classes class_name in
          (try 
            let (_,t) =  List.find (fun (att, typ) -> att=s ) c.attributes in
            t
          with
            |Not_found -> error "Attribut innexistant")
      
        |_ -> error "Accès attribut pour type qui n'est pas un objet de classe"
      )
    | _ -> failwith "case not implemented in type_mem_access"
  in

  let rec check_instr i ret tenv = match i with
    | Print e -> check e TInt tenv
    | Expr(e) -> check e TVoid tenv
    | Return(e) -> 
      if (ret = TVoid) then error "Pas de return pour un retour de type void"
      else
      let t = type_expr e tenv in
      if t <> ret then type_error t ret

    | Set(mem_acc, e) ->
      let te = type_expr e tenv in 
      let t = type_mem_access mem_acc tenv in

      (* maintenant on teste l'égalité stricte mais après faut voir
      si c'est un sous type avec l'héritage*)
      if te <> t then type_error te t
    | If(e, s1, s2) -> 
      check e TBool tenv;
      check_seq s1 ret  tenv;
      check_seq s2 ret  tenv
    | While(e, s) -> 
      check e TBool tenv;
      check_seq s ret  tenv
    | _ -> failwith "case not implemented in check_instr"
  and check_seq s ret tenv =
    List.iter (fun i -> check_instr i ret tenv) s
  in

  let rec check_class c tenv = 
    (* les attributs doivent être visibles pour les méthodes*)
    obj_courant := (TClass c.class_name);
    let tenv = add_env c.attributes tenv in
    List.iter (fun m -> check_mdef m tenv ) c.methods
    
  and check_mdef m tenv =
    let tenv = add_env m.params tenv in
    let tenv = add_env m.locals tenv in

    check_seq m.code m.return tenv;

    if(m.return <> TVoid && not(return_seq m.code)) then error "Manque un Return"
  
  
  (* pour les méthodes de type different de void on oblige le return *)
  and return_exist i = 
    match i with 
      | Print _ -> false
      | Set _ -> false
      | If (_ , s1 , s2 ) -> return_seq s1 && return_seq s2
      | While _ -> false
      | Return _ -> true
      | Expr _ -> false
  and return_seq seq = 
      match seq with 
        | [] -> false
        | i :: s -> return_exist i || return_seq s
  in

  let tenv = add_class_env p.classes tenv in
  List.iter (fun c_def -> check_class c_def tenv) p.classes;
  (* Là on parcouru toutes les classes donc si après on trouve une utilisation
  de this il faut lever une erreur 
  
  - Le flag pour savoir si on utilise un this en dehors d'une classe c'est 
  la valeur de TClasse soit this *)
  obj_courant := (TClass "this");
  check_seq p.main TVoid tenv
