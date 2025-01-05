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

let typecheck_prog p =
  let tenv = add_env p.globals Env.empty in
  (* pour garder dans this la classe de l'objet courant*)
  let obj_courant = ref (TClass "this") in

  let add_class_env l env = 
    List.fold_left (fun env class_def -> 
      if(Env.mem class_def.class_name env) then error "Deux classes avec le même nom"
      else
        Env.add class_def.class_name (TClass class_def.class_name) env
      ) env l
  in
  (**)
  let get_class (l: class_def list) (class_name:string): class_def = 
    try List.find (fun class_d -> class_d.class_name = class_name) l
    with Not_found -> error ("Missing declaration of the class " ^ class_name) 
  in
  
  let rec ascendent_fold application cls = 
    let res = application cls in
    if res <> None then res
    else 
     let o =  get_class p.classes cls in
      (
      match o.parent with 
       None -> application cls
      | Some c -> ascendent_fold application c
      )
  in
(* 
  let rec subtype tho' tho =
    if tho' = tho then true
    else match tho', tho with 
      TClass s', TClass s -> 
        if s' = s then true 
        else 
          let o = List.find (fun o -> o.class_name = s') p.classes in
          (match o.parent with 
            None -> false
            | Some tho' -> subtype (TClass tho') tho)
      | _ -> false
  in *)

  let subtype tho' tho = 
    match tho' with 
    TClass tho' ->  
        (
        ascendent_fold (
        fun tho_a ->  
          if TClass tho_a = tho then Some true
          else None
        )
        tho'
        )
        <> None 
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
    | Binop (Add, e1, e2) -> check e1 TInt tenv ; check e2 TInt tenv; TInt
    | Binop (Eq, e1, e2) |  Binop (Neq, e1, e2) -> 
      let tho1 = type_expr e1 tenv in
      let tho2 = type_expr e2 tenv in
      if tho1 = tho2  then TBool
      else type_error tho2 tho1     
    | Binop(_, e1, e2) -> check e1 TInt tenv ; check e2 TInt tenv; TInt
    | Get mem_acc -> type_mem_access mem_acc tenv
    | This ->
        (match (!obj_courant) with 
        TClass "this" -> error "Utilisation de this hors classe"
        |_ -> !obj_courant)
    | New cn -> type_constructor cn None
    | NewCstr (s, el) -> type_constructor s (Some el)
    
    | MethCall(e, s, el) ->
      match(type_expr e tenv) with
        | TClass c -> type_method s el c
        | tho -> error ("Incompatible object type " ^ (typ_to_string tho))

    and type_method s el c =
      let rec loop el ltypes = 
        match el, ltypes with 
        [], [] -> ()
        | e::el, (_, tho)::ltypes ->
          let tho' = type_expr e tenv in
          if not (subtype tho' tho) then type_error tho' tho
          ; loop el ltypes
        | _ -> error ("No method " ^ s ^ " found.")
      in
      let app tho =
        let methods =  (get_class p.classes tho).methods in
        try
          let o = List.find (fun obj -> obj.method_name = s) methods in
          loop el o.params; 
          Some o.return
        with Not_found -> None
      in
      match (ascendent_fold app c) with 
      Some v -> v
      | None ->  error ("Missing declaration of the method " ^ s)
  
    and type_constructor s le =
      let app tho = 
        match le with 
        None -> Some (TClass s)
      | Some le ->  
        try let tho = type_method "constructor" le tho in
          if TVoid <> tho then error (s ^ "(constructor expected to be of type" ^ (typ_to_string TVoid) ^ " but found, " ^(typ_to_string tho))
          else Some (TClass s)
        with Error e -> None
      in
      match (ascendent_fold app s) with 
      Some v -> v
      | None ->  error ("Missing declaration of the method " ^ s) 
  
  and type_mem_access m tenv = match m with
    | Var s -> 
      (
      try Env.find s tenv
      with Not_found -> error ("Missing declaration of the variabel " ^ s)
      )
    | Field(e, s) ->       
      match type_expr e tenv with 
        TClass c -> 
          let app tho = 
          try 
            let o = List.find (fun o -> o.class_name = tho) p.classes in
            let _, tho = List.find (fun (s', tho) -> s' = s) o.attributes in
            Some tho  
          with Not_found -> None
          in
          (
            match ascendent_fold app c with 
              None -> error (c ^ " has no attribute name: " ^ s)
              | Some v -> v
          )
        | _ -> error ("e is not an object in e." ^ s)     
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

      if not (subtype te t) then type_error te t
    | If(e, s1, s2) -> 
      check e TBool tenv;
      check_seq s1 ret  tenv;
      check_seq s2 ret  tenv
    | While(e, s) -> 
      check e TBool tenv;
      check_seq s ret  tenv
      
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
