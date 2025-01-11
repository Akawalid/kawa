open Kawa

exception Error of string
let error s = raise (Error s)
let type_error ty_actual ty_expected =
  error (Printf.sprintf "expected %s, got %s"
           (typ_to_string ty_expected) (typ_to_string ty_actual))

module Env = Map.Make(String)
type tenv = typ Env.t
type programme_state = {mutable this_k_found: bool; mutable current_method: string; mutable evaluating_left_side_of_assign: bool}

(*this variable is used for detecting the use of 'this' keyword in a static method*)
let pg_state = {this_k_found = false; current_method = "main"; evaluating_left_side_of_assign = false}

let typecheck_prog p =
  (* pour garder dans this la classe de l'objet courant*)
  let get_class (class_name:string): class_def = 
    try List.find (fun class_d -> class_d.class_name = class_name) p.classes
    with Not_found -> error ("Missing declaration of the class " ^ class_name) 
  in
  
  let rec ascendent_fold application o =
    (*
      Cette fonction est fréquemment utilisée dans ce projet. 
      Elle fonctionne de manière similaire à List.fold_left, mais sur une hiérarchie de classes.
      
      Pour un objet donné de classe o, on remonte la hiérarchie en appliquant la fonction 'application'fournie en argument.
      On s'arrête dès que la fonction 'application' renvoie une valeur différente de None.
    *)
    let res = application o in
    if res <> None then res
    else 
      match o.parent with 
       None -> application o
      | Some c -> ascendent_fold application (get_class c)
    in

  let rec subtype tho' tho = 
    match tho' with 
    TClass tho' ->  
        (
        ascendent_fold (
          fun o ->  
            if TClass o.class_name = tho then Some true
            else None
        )
        (get_class tho')
        )
        <> None 
    
    | TArray typ' ->  
      (match tho with 
        TArray typ -> subtype typ' typ
      | _ -> false)
    | _-> tho' = tho (*si tho ou tho' sont des types de base*)
  in

  let rec check e typ tenv =
    let typ_e = type_expr e tenv in
    if typ_e <> typ then type_error typ_e typ

  and type_expr e tenv = match e with
    | Int _  -> TInt
    | Bool _ -> TBool
    | Unop (Opp, e) -> check e TInt tenv; TInt
    | Unop (Not, e) -> check e TBool tenv; TBool
    | Binop (And, e1, e2) | Binop (Or, e1, e2) -> check e1 TBool tenv; check e2 TBool tenv; TBool
    | Binop (Add, e1, e2) | Binop (Mul, e1, e2) | Binop (Div, e1, e2) |Binop (Rem, e1, e2) |Binop (Sub, e1, e2) -> check e1 TInt tenv ; check e2 TInt tenv; TInt
    | Binop (Eq, e1, e2) |  Binop (Neq, e1, e2) -> 
      let tho1 = type_expr e1 tenv in
      let tho2 = type_expr e2 tenv in
      if tho1 = tho2  then TBool
      else type_error tho2 tho1
    | Binop(Instanceof, e, Get (Var c)) -> 
      if not (List.exists (fun c_def -> c_def.class_name = c) p.classes) then error ( c ^ " is not a class.");
      (match type_expr e  tenv with 
        TClass _ -> TBool
        | v -> error ("Expected object, got " ^ (typ_to_string v));
      )
    | Binop(Instanceof, _, _) -> error "Expected class after instanceof, got an other expression"
    | Binop(_, e1, e2) -> check e1 TInt tenv ; check e2 TInt tenv; TBool
    | Get mem_acc -> type_mem_access mem_acc tenv
    | This -> pg_state.this_k_found <- true;
      (try  Env.find "this" tenv  
      with Not_found -> error "'this' keyword is used outside a class definition.")
    | New cn -> type_constructor cn None tenv
    | NewCstr (s, el) -> type_constructor s (Some el) tenv
    | MethCall (Get (Var c), s, el) when List.exists (fun c_def -> c_def.class_name = c) p.classes ->
      type_method s el (get_class c) tenv
    | MethCall(e, s, el) ->
      (match(type_expr e tenv) with
        | TClass c -> type_method s el (get_class c) tenv
        | tho -> error ("Incompatible object type " ^ (typ_to_string tho))
      )
    | Array li -> 
      (
        match li with
        [] -> error "Array can not be empty"
        | [e] -> type_expr e tenv
        | e::l -> 
          let tho = ref (type_expr e tenv) in
          List.iter (fun e -> 
            let tho' = type_expr e tenv in
            if not (subtype tho' !tho) then
              if not (subtype !tho tho') then error("Array elements must be homogenous, expetcted " ^ typ_to_string !tho ^ ",got " ^ typ_to_string tho')
              else tho := tho'
            ) l;
          TArray !tho
      ) 
    | NewArray(tho, li) -> 
      (*Le type d'un appel NewArray(TInt, [Some 9; Some 3; None; None]) est 
        TArray TArray TArray TArray TInt
      *)
      List.fold_left (fun acc e -> 
        (match e with 
        Some e -> check e TInt tenv
        | _ -> ()
        );
        TArray acc) 
        tho
        li

    and check_arguments meth_name el ltypes tenv = 
      (*vérifie la cohérence de typage de chaque expression de el avec son type correspondent dans ltypes*)
      match el, ltypes with 
      [], [] -> ()
      | e::el, (_, tho)::ltypes ->
        let tho' = type_expr e tenv in
        if not (subtype tho' tho) then type_error tho' tho
        ; check_arguments meth_name el ltypes tenv
      | _, [] -> error ("Expected less arguments in method " ^ meth_name)  
      | [], (arg, tho)::_ -> error ("Missing argument " ^ arg ^ ": " ^ (typ_to_string tho) ^ "in method " ^ meth_name) 

      and check_visibility target_class entity_name entity_visibility env = 
        (* 
          Exemple pour comprendre le fonctionnement : 
          class A {
            o = new B()
            o.x
          }
          class B extends C {}
          class C { attribute private x }
      
          Dans ce cas :
            - target_class : C (classe contenant l'attribut)
            - entity_name : "x" (nom de l'attribut)
            - entity_visibility : "private" (visibilité de l'attribut)
            - env = {"this" -> A, ...} (environnement des types)
        *)
        try match Env.find "this" env with 
          TClass invoking_class -> 
              if entity_visibility = Private && invoking_class <> target_class (* appel depuis une classe externe *) then 
                  error (entity_name ^ " has private access in " ^ target_class)
              else if entity_visibility = Protected && not (subtype (TClass invoking_class)  (TClass target_class))then 
                  error (entity_name ^ " has protected access in " ^ target_class)
          | _ -> failwith "Typechecker issue"
        with Not_found (* appel depuis la méthode principale *) ->
              if entity_visibility = Private then 
                error (entity_name ^ " has private access in " ^ target_class) 
              else if entity_visibility = Protected then 
                error (entity_name ^ " has protected access in " ^ target_class)
      
    and type_method s el o tenv =
      (*
        s: method name
        el: parameters list
        o: class_def
        return: method type if well defined
      *)
      let app o =
        try let o' = List.find (fun obj -> obj.method_name = s) o.methods in
          (*
          vérification de visibilité de la fonction, 
            o.classname: classe ou la méthode se trouves 
            s: nom de la method
            o'.visibility: visibilité de la méthode
          *)
          check_visibility o.class_name s o'.visibility tenv;
          (*
          Vérificaiton de la cohérence des arguments
          C(f) = (t1 x ... x tN) -> t      E |- ek : tk'      tk' <: tk
          *)
          check_arguments s el o'.params tenv;
          Some o'.return
        with Not_found ->
          (*On vérifie dans les méthodes statiques de la meme manière*) 
          try let o' = List.find (fun obj -> obj.method_name = s) o.s_methods in
            check_visibility o.class_name s o'.visibility tenv;
            check_arguments s el o'.params tenv;
            Some o'.return
          with Not_found -> None
      in
        match (ascendent_fold app o) with 
        Some v -> v
        | None ->  error ("Missing declaration of the method " ^ s)
  
    and type_constructor cons_name el tenv = 
      (*Vérifie si l'appel au constructeur cons_name est cohérent avec son type*) 
        match el with 
        None -> TClass cons_name
      | Some el ->  
        try
          let o = List.find (fun obj -> obj.method_name = "constructor") (get_class cons_name).methods in
          check_arguments "constructor" el o.params tenv;
          (*L'assertion suivant est vérifiée dans check_mdef*)
          assert (o.return = TVoid && o.visibility = PackagePrivate);
          TClass cons_name
        with Not_found -> error ("Missing declaration of the constructor")
            
    and type_mem_access m tenv = match m with
    | Var s -> 
      (
      try Env.find s tenv
      with Not_found -> error ("Missing declaration of the variable " ^ s)
      )

    | Field (Get (Var c), s) when List.exists (fun c_def -> c_def.class_name = c) p.classes ->
      (*pour traiter le cas des appels static*)
      let app o = 
        try 
          let _, tho, visibility, _, _ = List.find (fun (s', _, _, _, _) -> s' = s) o.s_attributs in
          (*
            une fois qu'on trouve l'attribut, on vérifie sa visibilité. 
            Java s'arrête à la première occurrence d'une variable, même si sa visibilité est incohérente,  
            et ignore les occurrences avec une visibilité valide plus haut dans la hiérarchie.
          *)
          check_visibility o.class_name s visibility tenv;
          Some tho
        with Not_found -> None
        in
        ( 
          match ascendent_fold app (get_class c) with 
            None -> error (c ^ " has no static attribut name: " ^ s)
            | Some v -> v
        )
    | Field(e, attribut_name) ->    
      (match type_expr e tenv with
        TClass class_name -> 
          let app o = 
          try 
            let _, tho, visibility, final, _ = List.find (fun (s', _, _, _, _) -> s' = attribut_name) o.attributes in
            (*
                La vérification des variables immuables se fait en deux étapes :  
              - Etape statique : élimine quelques cas.  
              - Etape dynamique : à l'étape statique, sans les adresses des objets, on ne peut pas distinguer
                  entre l'initialisation de l'attribut final de l'objet en création et celle d'un autre objet de 
                  la même classe. Ce problème est résolu à l'étape dynamique. 
            *)

            let inside_class_name = 
              (try TClass class_name = Env.find "this" tenv
              with Not_found -> false) in
            if pg_state.evaluating_left_side_of_assign && final &&  (pg_state.current_method <> "constructor" || not(inside_class_name)) then error ("Immutable attribut " ^ attribut_name ^ " can not be modified or inintialised out of the constructor");
            
            (*
              une fois qu'on trouve l'attribut, on vérifie sa visibilité. 
              Java s'arrête à la première occurrence d'une variable, même si sa visibilité est incohérente,  
              et ignore les occurrences avec une visibilité valide plus haut dans la hiérarchie.
            *)
            check_visibility o.class_name attribut_name visibility tenv;
            Some tho
          with Not_found -> None
          in
          ( 
            (*
            On recherche l'attribut s de bas en haut avec la fonction ascendent_fold.  
            Remarque : le shadowing est correctement géré pour les attributs.
            *)
            match ascendent_fold app (get_class class_name) with 
              None -> error (class_name ^ " has no attribute name: " ^ attribut_name)
              | Some v -> v
          )  
        | _ -> error ("e is not an object in e." ^ attribut_name) 
      )
    | Tab(e, n) -> match type_expr e tenv with
          TArray a -> a
        | t -> error ("Expected an array, got " ^ typ_to_string t)
  in

  let rec check_instr i ret tenv = match i with
    | Print e -> check e TInt tenv
    | Expr(e) -> check e TVoid tenv
    | Return(e) -> 
      if (ret = TVoid) then error "incompatible types: unexpected return value."
      else
      let t = type_expr e tenv in
      if not (subtype t ret) then type_error t ret

    | Set(mem_acc, e) ->
      let te = type_expr e tenv in
      pg_state.evaluating_left_side_of_assign <- true;
      let t = type_mem_access mem_acc tenv in
      pg_state.evaluating_left_side_of_assign <- false;

      if not (subtype te t) then type_error te t;
    
    | If(e, s1, s2) -> 
      check e TBool tenv;
      check_seq s1 ret  tenv;
      check_seq s2 ret  tenv
    | If2(e, s) -> 
        check e TBool tenv;
        check_seq s ret tenv;
    | While(e, s) -> 
      check e TBool tenv;
      check_seq s ret  tenv
      
  and check_seq s ret tenv =
    List.iter (fun i -> check_instr i ret tenv) s
  in

  let rec check_class o tenv = 
    
    (*On vérifie le bon typages des methodes (meme les methodes statiques) dans le nouveau environement tenv
    qui contient:
      les parametres de la méthode
      les variables locals
    *)
    let tenv = Env.add "this" (TClass o.class_name) tenv in
    (*on vérifie si les initialisateurs des attributs sont cohérents avec leurs types*)
    List.iter (fun (_, tho, _, _, e) -> 
        match e with
        Some e -> check e tho tenv
        | None -> ()
    )
    o.attributes;
    
    (* On fait la même chose pour les attributs statiques, et ici on impose que l'initialisateur existe pour 
      les attributs statiques immuables. *)
    List.iter (fun (att_name, tho, _, final, e) -> 
      match e with
      Some e -> check e tho tenv
      | None -> if final then error ("Attrinbut " ^ att_name ^ " might not been initialized");()
    )
    o.s_attributs;

    List.iter (fun m -> check_mdef m tenv ) o.methods;
    List.iter (fun m -> check_s_mdef m tenv ) o.s_methods;
    

  and check_s_mdef m tenv =
    (*Vérification de la cohérence d'une méthode statique 'm' dans l'environement 'tenv'*)
    if m.method_name = "constructor" then error "constructor method can not be static";
    check_mdef m tenv;

    (*this_k_found est une variable globale qui indique si le mot clé 'this' est trouvé*)
    if pg_state.this_k_found then begin
      pg_state.this_k_found <- false; (*On le rénitialise à zero pour analyser les prochaines méthodes statiques*)
      error ("'this' keyword can not be referenced in a static method " ^ m.method_name)
    end

  and check_mdef m tenv =
    (*Vérification d'une méthode (non statique) dans l'environement local tenv (y compris le constructeur)*)

    pg_state.current_method <- m.method_name;
    (*constructeur doit avoir un type de retour VOID et une visibilité PackagePrivate (en JAVA c'est l'abscence du mot clé de visibilité)*)
    if m.method_name ="constructor"           
       && (m.return <> TVoid || m.visibility <> PackagePrivate) 
    then error "constructor can not have a restricted visibility (Private/Protected)."; 
    
    (* On vérifie que les paramètres et les variables locales sont tous distincts deux à deux. 
      De plus, on vérifie la cohérence des initialisateurs des variables locales avec leurs types. *)
    let container = Hashtbl.create 16 in
    List.iter (fun (s, _) -> 
        if Hashtbl.mem container s then error ("Multiple declarations of the parameter " ^ s ^ " in method " ^ m.method_name)
        else Hashtbl.add container s () 
      ) 
      m.params;
    
    List.iter (fun (s, tho, e) -> 
        if Hashtbl.mem container s then error ("Multiple declarations of the local variable " ^ s ^ " in method " ^ m.method_name);
        (match e with 
        None -> ()
        | Some e -> check e tho tenv)
        )
      m.locals;
    
    (*
      Pour vérifier le code de la fonction, on crée un nouvel environement qui contiendera:
        l'ancien environement
        les parametres
        les variables locals   
      Le shadowing est respecté : si un nom d'attribut se trouve parmi les paramètres ou les variables locales, ce sont ces derniers qui seront pris en priorité.
      
    *)
    
    let tenv = 
      (*on rajoute les variables locales et les paramètres à l'environement*)
      List.fold_left
      (fun env (x, t, _) -> Env.add x t env)
      ( List.fold_left
        (fun env (x, t) -> Env.add x t env)
        tenv 
        m.params
      )
      m.locals
    in
    check_seq m.code m.return tenv;
    if(m.return <> TVoid && not(close m.code)) then error ("Missing return statement in method " ^ m.method_name)   
  
  and close seq = 
    (*une séquence est close ssi toutes les branches possibles se terminent par un return*)
    match seq with 
    | [] -> false
    | i :: s -> 
        (match i with 
      | Print _ -> false
      | Set _ -> false
      | If (_ , s1 , s2 ) -> close s1 && close s2
      | If2 (_ , s) -> false
      | While (_, s) ->  close s
      | Return _ -> true
      | Expr _ -> false
      )
      || close s
  in
  let tenv = 
    List.fold_left (fun env (x, t, init) -> 
      if Env.mem x env then error ("global variable " ^ x ^ " is already defined")
      else begin
        (match init with
          None -> ()
          | Some init -> check init t env
        );
        Env.add x t env
      end
      )
     Env.empty
     p.globals
  in
  List.iter (fun c_def -> check_class c_def tenv) p.classes;
  check_seq p.main TVoid tenv
