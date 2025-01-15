open Kawa

exception Error of string
let error s = raise (Error s)
let type_error ty_actual ty_expected =
  error (Printf.sprintf "expected %s, got %s"
           (typ_to_string ty_expected) (typ_to_string ty_actual))

module Env = Map.Make(String)
type tenv = typ Env.t
type programme_state = {
    mutable this_k_found: bool;
    mutable current_method: string;
    mutable evaluating_left_side_of_assign: bool;
    checked_classes: (string, unit) Hashtbl.t;
    abstract_methods: (string, abstract_method_def) Hashtbl.t;
  }

(*this variable is used for detecting the use of 'this' keyword in a static method*)
let pg_state = {
    this_k_found = false; 
    current_method = "main"; 
    evaluating_left_side_of_assign = false;
    checked_classes = Hashtbl.create 16;
    abstract_methods = Hashtbl.create 16;
  }

let typecheck_prog p =
  (* pour garder dans this la classe de l'objet courant*)
  let get_class (class_name:string): class_def = 
    try List.find (fun class_d -> class_d.class_name = class_name) p.classes
    with Not_found -> error ("Missing declaration of the class " ^ class_name) 
  in

  let method_to_string m typs ret = m ^ ": (" 
  ^ (String.concat " * " (List.map (fun tho -> typ_to_string tho) typs)) ^ ")" ^ 
    (if List.is_empty typs then typ_to_string ret
    else "->" ^ (typ_to_string ret))
  in

  let levenshtein_distance s t =
    (*Algorithm de levenshtein en algorithmique dynamique, calcule en O(|s| * |t|)
      utilisé dans l'extension de correction 'Did you mean recursion?'
    *)
    let m = String.length s in
    let n = String.length t in
  
    let d = Array.make_matrix (m + 1) (n + 1) 0 in
  
    for i = 1 to m do
      d.(i).(0) <- i
    done;
    
    for j = 1 to n do
      d.(0).(j) <- j
    done;
  
    for i = 1 to m do
      for j = 1 to n do
        let substitution_cost = if s.[i - 1] = t.[j - 1] then 0 else 1 in
        d.(i).(j) <- min (min (d.(i - 1).(j) + 1)
                          (d.(i).(j - 1) + 1)) 
                          (d.(i - 1).(j - 1) + substitution_cost)
      done
    done;
  
    d.(m).(n)
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
    | TNull ->       
      (match tho with 
        TClass _ -> true
      | _ -> false)
    | _-> tho' = tho (*si tho ou tho' sont des types de base*)
  in

  let rec check e typ tenv =
    let typ_e = type_expr e tenv in
    if typ_e <> typ then type_error typ_e typ

  and type_expr e tenv = match e with
    | Int _  -> TInt
    | NullPtr -> TNull
    | Bool _ -> TBool
    | Unop (Opp, e) -> check e TInt tenv; TInt
    | Unop (Not, e) -> check e TBool tenv; TBool
    | Binop (And, e1, e2) | Binop (Or, e1, e2) -> check e1 TBool tenv; check e2 TBool tenv; TBool
    | Binop (Add, e1, e2) | Binop (Mul, e1, e2) | Binop (Div, e1, e2) |Binop (Rem, e1, e2) |Binop (Sub, e1, e2) -> check e1 TInt tenv ; check e2 TInt tenv; TInt
    | Binop (Eq, e1, e2) |  Binop (Neq, e1, e2) -> 
      let tho1 = type_expr e1 tenv in
      let tho2 = type_expr e2 tenv in
      let is_class typ = match typ with TClass _ -> true | _ -> false in
      if tho1 = tho2  || (tho1 = TNull && is_class tho2)|| (tho2 = TNull && is_class tho1) then TBool
      else type_error tho2 tho1
    | Binop(Instanceof, e, Get (Var c)) -> 
      if not (List.exists (fun c_def -> c_def.class_name = c) p.classes) then error ( c ^ " is not a class.");
      (match type_expr e tenv with 
        TClass _ | TNull -> TBool
        | v -> error ("Expected object, got " ^ (typ_to_string v));
      )
    | Binop(Instanceof, _, _) -> error "Expected class after instanceof, got an other expression"
    | Binop(_, e1, e2) -> check e1 TInt tenv ; check e2 TInt tenv; TBool
    | Get mem_acc -> type_mem_access mem_acc tenv
    | This -> pg_state.this_k_found <- true;
      (try  Env.find "this" tenv  
      with Not_found -> error "'this' keyword is used outside a class definition.")
    | New cn -> 
        (*Avant de vérifier si l'appel au constructeur est  valide, on vérifie si la classe est abstraite*)
        let o = get_class cn in
        if o.is_abstract then error ("Can not instanciate an abstract class " ^ cn);
        check_constructor o None tenv; TClass cn
    | NewCstr (cn, el) -> 
      (*Avant de vérifier si l'appel au constructeur est  valide, on vérifie si la classe est abstraite*)
      let o = get_class cn in
      if o.is_abstract then error ("Can not instanciate an abstract class " ^ cn);
      check_constructor o (Some el) tenv; TClass cn
    | MethCall (Get (Var c), s, el) when List.exists (fun c_def -> c_def.class_name = c) p.classes ->
      type_method s el (get_class c) tenv
    | MethCall(e, s, el) ->
      (match(type_expr e tenv) with
        | TClass c -> type_method s el (get_class c) tenv
        | tho -> error ("Incompatible object type " ^ (typ_to_string tho))
      )
    | Array li ->
      (*
        on utilise la regle d'inférence: 
              Gamma  |-  ek: tho (Vk)
        ------------------------------------
        Gamma  |-  [e1; ...; en]: TArray tho
      *)
      (
        match li with
        [] -> error "Array can not be empty"
        | [e] -> 
          (*s'il y a un seul element du tableau alors le type est simplement TArray(type e)*)
          TArray (type_expr e tenv)
        | e::l ->
          (*on cherche le type le plus générale tho tel, que tout les elements sont de type/sous-type de tho
          comme une recherche d'un maxiomaume dans un tableau
          *)
          (*initialise tho au premier element du tableau*)
          let tho = ref (type_expr e tenv) in
          List.iter (fun e -> 
            let tho' = type_expr e tenv in
            if not (subtype tho' !tho) then
              if not (subtype !tho tho') then
                (*si tho' n'est pas sous type de tho et tho n'est pas sous type de tho' alors erreur*)
                error("Array elements must be homogenous, expetcted " ^ typ_to_string !tho ^ ",got " ^ typ_to_string tho')
              else 
                (*si tho est un sous-type de tho' alors tho' est plus géénrale que les élements déja lu, donc on mis à jour tho*)
                tho := tho'
            ) l;
            (*l'invarient de cette bocle est, tho est le type le plus générale des élemetns déja visités*)
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
      
      (*
        'levenshtein_correction' est utilisée pour l'extension de correction "Did you mean recursion?".
        Le principe est simple : on sélectionne le mot le plus proche en termes de distance de Levenshtein, avec une tolérance maximale de 2, afin d'obtenir des résultats relativement similaires au mot donné par l'utilisateur.
        C'est pour cette raison que nous avons initialisé la distance à 3.
      *)
      let levenshtein_correction = ref (3, None) in
      let app o =
        try let o' = 
          List.find 
          (fun obj ->
          if  obj.method_name = s then  true
          else begin
            let lev = levenshtein_distance  obj.method_name s in 
            let min, _ = !levenshtein_correction in
            if lev < min then levenshtein_correction := (lev, Some obj.method_name);
            false
          end
          ) 
          o.methods 
          in
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
          try let o' = 

            List.find         
            (
            fun obj ->
            if  obj.method_name = s then  true
            else begin
              let lev = levenshtein_distance  obj.method_name s in 
              let min, _ = !levenshtein_correction in
              if lev < min then levenshtein_correction := (lev, Some obj.method_name);
              false
            end
            ) 
            o.s_methods in

            check_visibility o.class_name s o'.visibility tenv;
            check_arguments s el o'.params tenv;
            Some o'.return
          with Not_found -> None
      in
        match (ascendent_fold app o) with 
        Some v -> v
        | None ->  
          match !levenshtein_correction with 
          | _, None -> error ("Missing declaration of the method " ^ s)
          | _, Some approx -> error ("Missing declaration of the method " ^ s ^ ". Did you mean " ^ approx)
  
    and check_constructor class_obj el tenv = 
      (*
        class_obj: objet de la classe pour laquelle vérifier la cohérence de l'appel au constructeur
        el: liste des arguments effectifs
        tenv: l'environement local dans lequel l'évluation des parametres se fait
      *)
      (*Vérifie si l'appel au constructeur cons_name est cohérent avec son type*) 
        match el with 
        None -> ()
      | Some el ->  
        try
          (*mle constructeur doit exister pour pouvoir etre appelé*)
          let o = List.find (fun obj -> obj.method_name = "constructor") class_obj.methods in
          
          (*Les constructeurs doivent avoir des arguments effectifs cohérents avec les arguments formels, comme les méthodes.*)
          check_arguments "constructor" el o.params tenv;
          
         (*Ce qui nous assure de la validité de cette assertion est la fonction check_mdef.*)
          assert (o.return = TVoid && o.visibility = PackagePrivate);
          ()
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
          with Not_found -> 
            try let _ = List.find (fun (s', _, _, _, _) -> s' = attribut_name) o.s_attributs in
            error ("Can not access a static attribut from an object: " ^ attribut_name); 
            with Not_found -> None
          in
          ( 
            (*
            On recherche l'attribut s de bas en haut avec la fonction ascendent_fold.  
            Remarque : le shadowing est correctement géré pour les attributs.
            *)
            match ascendent_fold app (get_class class_name) with 
              None -> error (class_name ^ " has no (non static) attribute name: " ^ attribut_name)
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
    (*on rajoute la classe au classes déja véréfiées*)
    Hashtbl.add pg_state.checked_classes o.class_name ();

    (*on mis à jour l'association "this" -> nom de cette classe dans tenv*)
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
      | None -> if final then error ("Attribut " ^ att_name ^ " might not been initialized");()
    )
    o.s_attributs;

    (*
    On vérifie maintenant l'abstraction,  si la classe n'est pas abstraite =(implique)=> 
      1. aucune méthode abstraite. 
      2. Redéfinit toutes les méthodes abstraites des superclasses non encore redéfinies.
    
     Pour simplifier et rendre la vérification de l'abstraction plus efficace, il serait préférable de
     vérifier la validité de l'abstraction au niveau des superclasses en premier.
     Parcourir récursivement les superclasses en priorité (similaire à un fold_right, mais verticalement).
     
     Pour chaque classe :
        Vérifier la validité de l'invariant suivant : "Une classe n'est pas abstraite =(implique)=> elle ne doit 
        contenir aucune méthode abstraite."
        
        Si la classe est abstraite, ajouter toutes ses méthodes abstraites à une structure globale pour 
        s'assurer que les sous-classes les implémentent.
        
        Retirer de cette structure globale les méthodes abstraites qui ont été concrétisées par la classe 
        courante (cela permet de ne garder que les méthodes encore abstraites).
    
        mettre la classe courante comme vérifiée, pour ne pas la revérifiée dans la boucle à l'avant dernière 
        ligne de ce code
    
    *)

    (match o.parent with 
    None -> () 
    | Some cn -> check_class (get_class cn) tenv
    );

   (*On vérifie le bon typages des methodes (meme les methodes statiques) dans le nouveau environement tenv
    qui contient:
      les parametres de la méthode
      les variables locals
    *)

    List.iter (fun abs_mobj -> Hashtbl.add pg_state.abstract_methods abs_mobj.abs_method_name abs_mobj) o.abstract_methods;
    
    List.iter (fun m -> check_mdef m tenv ) o.methods;
    List.iter (fun m -> check_s_mdef m tenv ) o.s_methods;

    if not o.is_abstract 
      &&
       Hashtbl.length pg_state.abstract_methods > 0 
    then
    error ("class " ^ o.class_name ^ " is not abstract and does not override " 
      ^ Hashtbl.fold (fun s m acc -> 
        (method_to_string s  m.abs_params m.abs_return)
        ^  ", " ^ acc) 
        pg_state.abstract_methods
         ""
    );

  and check_s_mdef m tenv =
    (*Vérification de la cohérence d'une méthode statique 'm' dans l'environement 'tenv'*)
    if m.method_name = "constructor" then error "constructor method can not be static";
    common_verifecation m tenv;

    (*this_k_found est une variable globale qui indique si le mot clé 'this' est trouvé*)
    if pg_state.this_k_found then begin
      pg_state.this_k_found <- false; (*On le rénitialise à zero pour analyser les prochaines méthodes statiques*)
      error ("'this' keyword can not be referenced in a static method " ^ m.method_name)
    end

  and check_mdef m tenv =
    (*Vérification d'une méthode (non statique) dans l'environement local tenv (y compris le constructeur)*)

    (*constructeur doit avoir un type de retour VOID et une visibilité PackagePrivate (en JAVA c'est l'abscence du mot clé de visibilité)*)
    if m.method_name ="constructor"           
       && (m.return <> TVoid || m.visibility <> PackagePrivate) 
    then error "constructor can not have a restricted visibility (Private/Protected)."; 
    
    common_verifecation m tenv;
    (*
      Cette partie traite les méthodes et classes abstraites, c'est partie 3 de l'algorithm énnoncé dans la fonction
      check_class 
        (petit rappel: 
              Retirer de cette structure globale les méthodes abstraites qui ont été concrétisées par la classe 
              courante (cela permet de ne garder que les méthodes encore abstraites).
        )
      
      fonctionnement de l'algorithme :
      Dans la structure globale, on stocke les méthodes abstraites sous forme d'une hashtable où les clés sont les noms des méthodes,
      et la valeur associée est l'objet de la méthode abstraite. Le problème est que plusieurs méthodes peuvent avoir le même nom.
      Ainsi, dans la table de hachage, plusieurs associations peuvent être cachées derrière une seule entrée : 
      nom_méthode -> objet_méthode.

      L'idée de l'algorithme est de trouver toutes les associations correspondant au nom de la méthode courante (m.methode_name)
      en utilisant la fonction Hashtbl.find_all. Ensuite, on supprime toutes les associations de la méthode courante dans la table
      de hachage, puis on réinsère uniquement les méthodes dont la signature est différente de celle de la méthode courante.
      
      Alternative : ce serait plus intéressant de créer une fonction de hachage qui prend en compte toute la signature à la fois,
      mais cela compliquerait le code en termes de lecture et de compréhension.

    *)

    let l_methods_with_same_name = Hashtbl.find_all pg_state.abstract_methods m.method_name in
    let predicat meth_obj = 
      meth_obj.abs_return = m.return 
      &&    
      (try (List.for_all2 (fun tho1 (_, tho2) -> tho1 = tho2) meth_obj.abs_params m.params)
      with Invalid_argument _ -> false
      )
     in
      
    let rec update_hash_tbl predicat l_bindigs_of_key = 
      match l_bindigs_of_key with 
      [] -> assert (not (Hashtbl.mem pg_state.abstract_methods m.method_name)); ()
      | h::tl -> 
        let key = m.method_name in
        if Hashtbl.mem pg_state.abstract_methods key then Hashtbl.remove pg_state.abstract_methods key;
        update_hash_tbl predicat tl;
        if not (predicat h) then Hashtbl.add pg_state.abstract_methods key h
    in 
    update_hash_tbl predicat l_methods_with_same_name

  and common_verifecation m tenv = 
    pg_state.current_method <- m.method_name;
    (*
      c'est une fonction de vérification commune entre 'check_mdef' et 'check_s_mdef', pour véréfier la validité des parametrer et de variables locales
      de la méthode
    *)

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
      if(m.return <> TVoid && not(close m.code)) then error ("Missing return statement in method " ^ m.method_name);     

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
  (*
  En rajoutant les variables globales à l'environnement, on vérifie en parallèle s'il existe des variables ayant le même nom. 
  Si c'est le cas, une erreur est levée !
*)
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
  List.iter (fun c_def -> 
    (*on ne traite que les classes qui n'ont pas été déja traitées*)
    if not (Hashtbl.mem pg_state.checked_classes c_def.class_name) then begin 
      check_class c_def tenv;
      (*on réinitialise la table des méthodes abstraites pour les prochaines classes*)
      Hashtbl.reset pg_state.abstract_methods
    end
  ) 
  (* Il est plus optimisé de parcourir la liste des classes de la fin vers le début, car généralement les superclasses apparaissent en premier. 
   La version la plus optimisée de notre algorithme consiste à appliquer un tri topologique sur les classes.
   puisque, cette solution complexifie trop la structure du code, on peut réduire légèrement la complexité 
   en parcourant les classes de la fin vers le début. *)
  (List.rev p.classes);

  check_seq p.main TVoid tenv
