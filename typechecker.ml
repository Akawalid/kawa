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
  (**)
  let get_class (l: class_def list) (class_name:string): class_def = 
    try List.find (fun class_d -> class_d.class_name = class_name) l
    with Not_found -> error ("Missing declaration of the class " ^ class_name) 
  in
  
  let rec ascendent_fold application o =
    let res = application o in
    if res <> None then res
    else 
      match o.parent with 
       None -> application o
      | Some c -> ascendent_fold application (get_class p.classes c)
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
          fun o ->  
            if TClass o.class_name = tho then Some true
            else None
        )
        (get_class p.classes tho')
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
    | Binop (And, e1, e2) | Binop (Or, e1, e2) -> check e1 TBool tenv; check e2 TBool tenv; TBool
    | Binop (Add, e1, e2) | Binop (Mul, e1, e2) |Binop (Div, e1, e2) |Binop (Rem, e1, e2) |Binop (Sub, e1, e2) -> check e1 TInt tenv ; check e2 TInt tenv; TInt
    | Binop (Eq, e1, e2) |  Binop (Neq, e1, e2) -> 
      let tho1 = type_expr e1 tenv in
      let tho2 = type_expr e2 tenv in
      if tho1 = tho2  then TBool
      else type_error tho2 tho1
    | Binop(_, e1, e2) -> check e1 TInt tenv ; check e2 TInt tenv; TInt
    | Get mem_acc -> type_mem_access mem_acc tenv
    | This ->
      (try  Env.find "this" tenv  
      with Not_found -> error "'this' keyword is used outside a class definition.")
    | New cn -> type_constructor cn None
    | NewCstr (s, el) -> type_constructor s (Some el)
    
    | MethCall(e, s, el) ->
      match(type_expr e tenv) with
        | TClass c -> type_method s el (get_class p.classes c)
        | tho -> error ("Incompatible object type " ^ (typ_to_string tho))

    and type_method s el o =
      let rec loop el ltypes = 
        match el, ltypes with 
        [], [] -> ()
        | e::el, (_, tho)::ltypes ->
          let tho' = type_expr e tenv in
          if not (subtype tho' tho) then type_error tho' tho
          ; loop el ltypes
        | _ -> error ("No method " ^ s ^ " found.")
      in
      let app o =
        let methods =  o.methods in
        try
          let o = List.find (fun obj -> obj.method_name = s) methods in
          loop el o.params; 
          Some o.return
        with Not_found -> None
      in
      match (ascendent_fold app o) with 
      Some v -> v
      | None ->  error ("Missing declaration of the method " ^ s)
  
    and type_constructor s le =
      let app o = 
        match le with 
        None -> Some (TClass s)
      | Some le ->  
        try let tho = type_method "constructor" le o in
          if TVoid <> tho then error (s ^ "(constructor expected to be of type" ^ (typ_to_string TVoid) ^ " but found, " ^(typ_to_string tho))
          else Some (TClass s)
        with Error e -> None
      in
      match (ascendent_fold app (get_class p.classes s)) with 
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
          let app o = 
          try 
            let _, tho = List.find (fun (s', tho) -> s' = s) o.attributes in
            Some tho  
          with Not_found -> None
          in
          (
            match ascendent_fold app (get_class p.classes c) with 
              None -> error (c ^ " has no attribute name: " ^ s)
              | Some v -> v
          )
        | _ -> error ("e is not an object in e." ^ s)     
  in

  let rec check_instr i ret tenv = match i with
    | Print e -> check e TInt tenv
    | Expr(e) -> check e TVoid tenv
    | Return(e) -> 
      if (ret = TVoid) then error "'Return' keyword not expected for void type."
      else
      let t = type_expr e tenv in
      if not (subtype t ret) then type_error t ret

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

  let rec check_class o tenv = 
    (* les attributs doivent être visibles pour les méthodes*)
    let environement = ref (Env.add "this" (TClass o.class_name) Env.empty) in
    let app o = 
      environement := add_env  o.attributes (!environement);
      None
    in
    let _ = ascendent_fold app o in
    let tenv = !environement in
    List.iter (fun m -> check_mdef m tenv ) o.methods;
    
  and check_mdef m tenv =
    let tenv = add_env m.params (add_env m.locals tenv) in
    check_seq m.code m.return tenv;
    if(m.return <> TVoid && not(return_seq m.code)) then error ("Expected 'return' at the end of the method " ^ m.method_name)   
  
  (* pour les méthodes de type different de void on oblige le return *)
  and return_exist i = 
    match i with 
      | Print _ -> false
      | Set _ -> false
      | If (_ , s1 , s2 ) -> return_seq s1 && return_seq s2
      | While (_, s) ->  return_seq s
      | Return _ -> true
      | Expr _ -> false
  and return_seq seq = 
      match seq with 
        | [] -> false
        | i :: s -> return_exist i || return_seq s
  in
  
  List.iter (fun c_def -> check_class c_def tenv) p.classes;
  check_seq p.main TVoid tenv
