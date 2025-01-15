open Kawa

type value =
  | VInt  of int
  | VBool of bool
  | VObj  of obj option
  | VArr of value array
  | Null
and obj = {
  cls:    string;
  fields: (string, value) Hashtbl.t;
  f_fields: (string, value) Hashtbl.t;
} and t_cls_env = {
  st_attributs: (string, value) Hashtbl.t;
  f_attributs: (string, value) Hashtbl.t;
}

exception Error of string
exception Return of value

let exec_prog (p: program): unit =
  (*Table pour stqouer les variables globales*)
  let env = Hashtbl.create 16 in

  (*l'environement local, qui va servir au appels de méthodes*)
  let lenv = Hashtbl.create 16 in

  (*
  Pour stocker les valeures des variables statiques on creé un environement dans lequel les clés sont les 
  noms des classes et des tables de hachage d'attributs statiques sont les valeures.
  
  Pour le remplire on aura besoin de la fonction eval, pour évaluer les expression d'initialisation, 
  donc on le fera apres la déclaration de la fonction eval
  *)
  let class_env = Hashtbl.create 16 in
  (*Le rempissage des tables précédentes se fait à la fin de ce code, juste avant l'appel à exec_seq p.main*)
  
  let get_class c = 
    List.find (fun obj -> obj.class_name = c) p.classes
  in

  let error m = raise (Error m) in

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

  let rec eval_call f this args =
    let o = List.find (fun class_d -> class_d.class_name = this.cls
    ) p.classes in

    let app o = 
        try Some (List.find (fun meth_d -> meth_d.method_name = f) o.methods)
        with Not_found -> None
    in

    let meth = match (ascendent_fold app o) with 
    None-> failwith "Typechcker problem"
    | Some v -> v
    in

    (*ajout des parametres dans l'espace locale*)
    List.iter2 (fun (par, _) v  -> Hashtbl.add lenv par v) meth.params args;
    (*ajout des vars locals dans *)
    List.iter (fun (par, _, e) -> 
      match e with 
      None -> Hashtbl.add lenv par Null
      | Some e -> Hashtbl.add lenv par (eval e))
     meth.locals;
    
    (*We hide the current binding of this and associate it to the new class*)
    Hashtbl.add lenv "this" (VObj (Some this));
  
    let restore_context () =       
      (*restore the previous binding of this*)
      Hashtbl.remove lenv "this";
      (*Restauration des dernières valeurs pour le shadowing*)
      List.iter (fun (par, _)  -> Hashtbl.remove lenv par) meth.params;
      List.iter (fun (loc, _, _) -> Hashtbl.remove lenv loc) meth.locals;
    in
    try 
      exec_seq meth.code;
      (*dans le cas ou la méthode à un type de retour VOID donc ne lève pas une exception, on dépile quand meme
      le context*)
      restore_context()

    with Return v -> (
      restore_context ();
      raise (Return v)
    ); 
  
  and eval_call_s f cls args =
    (*evaluer un appel de méthode statique*)
    let o = List.find (fun class_d -> class_d.class_name = cls
    ) p.classes in
    let app o = 
        try Some (List.find (fun meth_d -> meth_d.method_name = f) o.s_methods)
        with Not_found -> None
    in
    let meth = match (ascendent_fold app o) with 
    None-> failwith "Typechcker problem"
    | Some v -> v
    in

    (*ajout des parametres dans l'espace locale*)
    List.iter2 (fun (par, _) v  -> Hashtbl.add lenv par v) meth.params args;
    (*ajout des vars locals dans *)
    List.iter (fun (par, _, e) -> 
      match e with 
      None -> Hashtbl.add lenv par Null
      | Some e -> Hashtbl.add lenv par (eval e)
      ) meth.locals;
    
    let restore_context () =       
      (*restore the previous binding of this*)
      Hashtbl.remove lenv "this";
      (*Restauration des dernières valeurs pour le shadowing*)
      List.iter (fun (par, _)  -> Hashtbl.remove lenv par) meth.params;
      List.iter (fun (loc, _, _) -> Hashtbl.remove lenv loc) meth.locals;
    in

    try exec_seq meth.code; 
      restore_context ()
    with Return v -> (
      restore_context ();
      raise (Return v)
    )

  and evali e = match eval e with
    | VInt n -> n
    | Null -> error "Trying to acces a non initialised variable"
    | _ -> assert false
  and evalb e = match eval e with
    | VBool b -> b
    | Null -> error "Trying to acces a non initialised variable"
    | _ -> assert false
  and evalo e = match eval e with
    | VObj o -> o
    | Null -> error "Trying to acces a non initialised variable"
    | _ -> assert false
  and evala e =  match eval e with
    | VArr a -> a
    | Null -> error "Trying to acces a non initialised variable"
    | _ -> assert false
      
  and eval (e: expr): value = match e with
    | Int n  -> VInt n
    | NullPtr -> VObj None
    | Bool b -> VBool b
    | Get (mem_acc) -> 
      (
        match mem_acc with 
        Var id -> 
          (
            (*on cherche la variable dans l'environement globale en première, s'il n'existe pas, on l'a cherche dans l'environement local*)
            let ret = (try Hashtbl.find lenv id
            with Not_found -> Hashtbl.find env id) in
            if ret = Null then error "Trying to access a non initialized memory";
            ret
          )
        | Field (Get (Var c), s) when List.exists (fun c_def -> c_def.class_name = c) p.classes ->
          (*cas d'un acces à une variable statique*)
          let c_env = (Hashtbl.find class_env c) in
          let ret = (try Hashtbl.find c_env.st_attributs s;
          with Not_found -> try Hashtbl.find c_env.f_attributs s
          with Not_found -> error ("Immuable attribute " ^ s ^ " is not initialised")) in
          if ret = Null then error "Trying to access a non initialized memory";
          ret
      
        | Field(eo, att) -> 
          let obj = evalo eo in
          (match obj with 
            None -> error "Trying to access a null pointer"
          | Some obj -> 
          let ret = (try Hashtbl.find obj.fields att  
          with Not_found -> 
            try 
              let tmp = Hashtbl.find obj.f_fields att in
              if Null = tmp then error ("Immuable attribute " ^ att ^ " is not initialised")
              else tmp
            with Not_found -> failwith "Problem interpreter"
          ) in
          if ret = Null then error "Trying to access a non initialized memory";
          ret        
          )
        | Tab (e, n) -> 
          (match eval e with 
              VArr a -> 
                (try let v = a.(n) in
                  if v <> Null then v
                  else error "Trying to access a non initialised memory."
                with Invalid_argument m -> error m)
              | _ -> failwith "Typechecker problem"
          )
      )
    | This -> Hashtbl.find lenv "this"
    | New cn ->
      let o = get_class cn in
      let fields = Hashtbl.create 16 in
      let f_fields = Hashtbl.create 16 in
      (*On initialise les attributs à Null*)
      let app o = 
        List.iter (fun (att, _, _, final, e) -> 
          if final then 
            match e with 
            None -> Hashtbl.add fields att Null
            | Some e -> Hashtbl.add fields att (eval e)  
          else 
            match e with 
            None -> Hashtbl.add f_fields att Null
            | Some e -> Hashtbl.add f_fields att (eval e)  
        ) o.attributes;
        None
      in
      let _ = ascendent_fold app o in
      VObj (Some {cls = o.class_name; fields = fields; f_fields = f_fields})
      
    | NewCstr (cn, el) -> 
      let o = get_class cn in
      let fields = Hashtbl.create 16 in
      let f_fields = Hashtbl.create 16 in
      (*On initialise les attributs à Null*)
      let app o = 
        List.iter (fun (att, _, _, final, e) -> 
          if not final then 
            (match e with 
            None -> Hashtbl.add fields att Null
            | Some e -> Hashtbl.add fields att (eval e)
            )
          else 
            (match e with 
            None -> Hashtbl.add f_fields att Null
            | Some e -> Hashtbl.add f_fields att (eval e)
            ) 
          ) o.attributes;
        None
      in
      let _ = ascendent_fold app o in
      let obj = {cls=o.class_name; fields=fields; f_fields = f_fields} in

     (* On appelle le constructeur pour agir sur l'objet créé *)
      eval_call "constructor" obj (List.map (fun e -> eval e) el);
      VObj (Some obj)
    | MethCall (Get (Var class_name), meth_name, el) when List.exists (fun c_def -> c_def.class_name = class_name) p.classes ->
      (
        try 
        eval_call_s meth_name class_name (List.map (fun e -> eval e) el);
        Null
        with Return v -> v)
    | MethCall (e, s, el) ->
      (try
        match evalo e with
        None -> error "Trying ot access a null pointer."
        | Some o -> 
        eval_call s o (List.map (fun e -> eval e) el);
        Null
      with Return v -> v)
      
    | Unop (Opp, e) -> 
      (match eval e with 
        VInt v -> VInt(-v)
        | _ -> failwith "Typechecker problem"
      )
    | Unop (Not, e) ->         
      (match eval e with 
        VBool v -> VBool(not v)
        | _ -> failwith "Typechecker problem"
      )
    | Binop (Add, e1, e2) -> 
      (match eval e1, eval e2 with 
        VInt v1, VInt v2 -> VInt(v1 + v2)
        | _ -> failwith "Typechecker problem"
      )
    | Binop (Sub, e1, e2) -> 
      (match eval e1, eval e2 with 
        VInt v1, VInt v2 -> VInt(v1 - v2)
        | _ -> failwith "Typechecker problem"
      )
    | Binop (Mul, e1, e2) -> 
      (match eval e1, eval e2 with 
        VInt v1, VInt v2 -> VInt(v1 * v2)
        | _ -> failwith "Typechecker problem"
      )
    | Binop (Div, e1, e2) -> 
      (match eval e1, eval e2 with 
        VInt v1, VInt v2 -> VInt(v1 / v2)
        | _ -> failwith "Typechecker problem"
      )
    | Binop (Rem, e1, e2) -> 
      (match eval e1, eval e2 with 
        VInt v1, VInt v2 -> VInt(v1 mod v2)
        | _ -> failwith "Typechecker problem"
      )
    | Binop (Eq, e1, e2) -> VBool (eval e1 = eval e2)  
    | Binop (Neq, e1, e2) -> VBool (eval e1 <> eval e2)  
    | Binop(Lt, e1, e2) -> 
      (match eval e1, eval e2 with 
      VInt v1, VInt v2 -> VBool(v1 < v2)
      | _ -> failwith "Typechecker problem"
      )
    | Binop(Le, e1, e2) -> 
      (match eval e1, eval e2 with 
      VInt v1, VInt v2 -> VBool(v1 <= v2)
      | _ -> failwith "Typechecker problem"
      )
    | Binop(Gt, e1, e2) ->
      (match eval e1, eval e2 with 
      VInt v1, VInt v2 -> VBool(v1 > v2)
      | _ -> failwith "Typechecker problem"
      ) 
    | Binop(Ge, e1, e2) ->
      (match eval e1, eval e2 with 
      VInt v1, VInt v2 -> VBool(v1 >= v2)
      | _ -> failwith "Typechecker problem"
      )
    | Binop(And, e1, e2) -> 
      (match eval e1, eval e2 with 
      VBool v1, VBool v2 -> VBool(v1 && v2)
      | _ -> failwith "Typechecker problem"
      )
    | Binop(Or, e1, e2) -> 
      (match eval e1, eval e2 with 
      VBool v1, VBool v2 -> VBool(v1 || v2)
      | _ -> failwith "Typechecker problem"
      )
    | Binop(Instanceof, e, Get (Var c)) -> 
      let obj = evalo e in
      (match obj with 
        None -> VBool false 
      | Some obj -> 
        (*Verify if the class associated to obj, is a subclass of c*)
        let app o = 
          if o.class_name = c then Some true
          else None
        in

        (match ascendent_fold app (get_class obj.cls) with 
          None -> VBool false
          | _ -> VBool true
        )
      )
    | Binop(Instanceof, _, _) -> failwith "Typechecker problem"
    | Array li -> 
      (*
        L'idée de l'algorithme est de créer le tableau avec Array.init tel que f(i) = eval ei,
        où ei est le i-ème élément de la liste.
        Pour accéder aux éléments, on met à jour la référence mli à chaque itération de Array.init,
        tel que mli := List.tl !mli, afin de pouvoir accéder aux éléments dans l'ordre en parallèle avec Array.init.
      *)
      let mli = ref li in
      VArr (
        Array.init (List.length li) 
        (fun i ->  
          let v = eval (List.hd !mli) in
          mli := List.tl !mli;
          v  
        )
      )
    | NewArray (tho, li) ->
      (*
        Ce matching crée un tableau initialement vide, rempli avec Null, de type tho[n1][n2]...[nk][]...[],
        où les dimensions sont données dans li. Par exemple, pour new int[5][6][][], 
        le constructeur sera de la forme NewArray(TInt, [Some 5; Some 6; None; None]).
      *)
      (let rec generat_arr li = 
        (match li with 
        | (Some e)::li -> 
          let dim = evali e in
          if dim = 0 then error "Array length can not be zero";
          VArr (Array.init dim (fun i -> generat_arr li))
        | _ -> Null
        )
  
      in
      if li = [] then failwith "Parser problem";
      generat_arr li)
  
  and exec (i: instr): unit = match i with
    | Print e -> Printf.printf "%d\n" (evali e)
    | Expr(e) -> let _ = eval e in () 
    | Return(e) -> raise (Return (eval e))

    | Set(mem_acc, e) ->
      let ve = eval e in
      (match mem_acc with 
        | Var s -> 
          if Hashtbl.mem lenv s then Hashtbl.replace lenv s ve
          else if Hashtbl.mem env s then  Hashtbl.replace env s ve 
          else failwith "Typechecker problem"
        
        | Field (Get (Var c), s) when List.exists (fun c_def -> c_def.class_name = c) p.classes ->
            let c_env = (Hashtbl.find class_env c) in
            if Hashtbl.mem c_env.st_attributs s then Hashtbl.replace c_env.st_attributs s (eval e)
            else if Hashtbl.mem c_env.f_attributs s then error ("Immuable attribute " ^ s ^ " can not be modified.")
            else failwith "Interpreter probelm, final static attribut not found"

        | Field(eo, s) -> 
          let obj = evalo eo in
          (match obj with 
          None -> error "Trying to access a null pointer." 
          | Some obj -> 
            if Hashtbl.mem obj.fields s then Hashtbl.replace obj.fields s (eval e)
            else 
              try 
                if Null <> Hashtbl.find obj.f_fields s then error ("Immuable attribute " ^ s ^ " can not be modified.")
                else Hashtbl.add obj.f_fields s (eval e)
              with  Not_found -> failwith "Problem interpreter."
               
          )
        | Tab(tab, n) -> 
          let a = evala tab in
          (try a.(n) <- eval e
          with Invalid_argument m -> error m)
      )
    | If(e, s1, s2) -> 
      if(evalb e) then exec_seq s1
      else exec_seq s2

    | If2(e, s) -> if(evalb e) then exec_seq s
      
    | While(e, s) -> 
      let ve = ref (evalb e) in

      while (!ve) do 
        exec_seq s;
        ve := evalb e;
      done;

  and exec_seq s = List.iter exec s
  in
  
  (*Remplissage de la table class_env, pour initialiser les attributes statiques de chaque classe*)
  let get_all_class_s_attributs c_def = 
    let fields = Hashtbl.create 16 in
    let f_fields = Hashtbl.create 16 in
    let app o = 
      List.iter (fun (n_att, _, _, f, e) -> 
        if not f then 
          (match e with 
          None -> Hashtbl.add fields n_att Null
          | Some e -> Hashtbl.add fields n_att (eval e)
          )
        else 
          (match e with 
          None -> failwith "Typechecker problem, static final must be initialised"
          | Some e -> Hashtbl.add f_fields n_att (eval e)
          )
      ) c_def.s_attributs;
      None
    in
    let _ = ascendent_fold app c_def in
    fields, f_fields
  in
  List.iter (
    fun c_def ->
      let h1, h2 = get_all_class_s_attributs c_def in 
      Hashtbl.add 
      class_env
      c_def.class_name 
      {
        st_attributs = h1;
        f_attributs = h2
      }
  ) p.classes;

  (*Remplissage de la tabledes variables globales avec leurs initialisation*)
  List.iter (fun (x, _, e) ->
    match e with 
    None -> Hashtbl.add env x Null
    | Some e -> Hashtbl.add env x (eval e) 
  ) p.globals;

  exec_seq p.main
  