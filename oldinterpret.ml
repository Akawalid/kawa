open Kawa

type value =
  | VInt  of int
  | VBool of bool
  | VObj  of obj
  | VArr of value array
  | Null
  | NotInitialised
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
  let env = Hashtbl.create 16 in
  List.iter (fun (x, _) ->
     Hashtbl.add env x Null) p.globals;

  let get_class c = 
    List.find (fun obj -> obj.class_name = c) p.classes
  in

  let default_value tho = 
    match tho with 
    TInt -> VInt 0
    | TBool -> VBool true
    | TClass _ -> Null
    | TArray _ -> Null 
    | TVoid -> failwith "Typechecker problem"
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

  (*
  Pour stocker les valeures des variables statiques on creé un environement dans lequel les clés sont les 
  noms des classes et des tables de hachage d'attributs statiques sont les valeures.
  *)

  let create_class_env = 
    let get_all_class_s_attributs c_def = 
      let fields = Hashtbl.create 16 in
      let app o = 
        List.iter (fun (n_att, _, _, f) -> if not f then Hashtbl.add fields n_att Null) c_def.s_attributs;
        None
      in
      let _ = ascendent_fold app c_def in
      fields
    in
    let class_env = Hashtbl.create 16 in
    List.iter (
      fun c_def -> 
        Hashtbl.add 
        class_env
        c_def.class_name 
        {
          st_attributs = get_all_class_s_attributs c_def;
          f_attributs = Hashtbl.create 16
        }
    ) p.classes;
    class_env
  in
  let class_env = create_class_env in

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
    let lenv = Hashtbl.create 16 in

    (*ajout des parametres dans l'espace locale*)
    List.iter2 (fun (par, _) v  -> Hashtbl.add lenv par v) meth.params args;
    (*ajout des vars locals dans *)
    List.iter (fun (par, _) -> Hashtbl.add lenv par Null) meth.locals;
    
    (*We hide the current binding of this and associate it to the new class*)
    Hashtbl.add lenv "this" (VObj this);
    exec_seq meth.code lenv;

    (*restore the previous binding of this*)
    Hashtbl.remove lenv "this";
    (*Restauration des dernières valeurs pour le shadowing*)
    List.iter2 (fun (par, _) v  -> Hashtbl.remove lenv par) meth.params args;
    List.iter (fun (par, _) -> Hashtbl.remove lenv par) meth.locals;
  
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
    let lenv = Hashtbl.create 16 in

    (*ajout des parametres dans l'espace locale*)
    List.iter2 (fun (par, _) v  -> Hashtbl.add lenv par v) meth.params args;
    (*ajout des vars locals dans *)
    List.iter (fun (par, _) -> Hashtbl.add lenv par Null) meth.locals;
    exec_seq meth.code lenv;

    (*Restauration des dernières valeurs pour le shadowing*)
    List.iter2 (fun (par, _) v  -> Hashtbl.remove lenv par) meth.params args;
    List.iter (fun (par, _) -> Hashtbl.remove lenv par) meth.locals;
  
  and exec_seq s lenv =
    (let rec evali e = match eval e with
      | VInt n -> n
      | _ -> assert false
    and evalb e = match eval e with
      | VBool b -> b
      | _ -> assert false
    and evalo e = match eval e with
      | VObj o -> o
      | _ -> assert false
    and evala e =  match eval e with
    | VArr a -> a
    | _ -> assert false
        
    and eval (e: expr): value = match e with
      | Int n  -> VInt n
      | Bool b -> VBool b
      | Get (mem_acc) -> 
        (
          match mem_acc with 
          Var id -> 
            (
              try Hashtbl.find lenv id
              with Not_found -> Hashtbl.find env id
            )
          | Field (Get (Var c), s) when List.exists (fun c_def -> c_def.class_name = c) p.classes->
            (*cas d'un acces à une variable statique*)
            let c_env = (Hashtbl.find class_env c) in
            (try Hashtbl.find c_env.st_attributs s;
            with Not_found -> try Hashtbl.find c_env.f_attributs s
            with Not_found -> error ("Immuable attribute " ^ s ^ " is not initialised"))
        
          | Field(eo, att) -> 
            let obj = evalo eo in
            (try Hashtbl.find obj.fields att  
            with Not_found -> try Hashtbl.find obj.f_fields att
            with Not_found -> error ("Immuable attribute " ^ att ^ " is not initialised"))
          | Tab (e, n) -> 
            (match eval e with 
                VArr a -> 
                  (try let v = a.(n) in
                    if v <> NotInitialised then v
                    else error "Trying to access a non initialised memory."
                  with Invalid_argument m -> error m)
                | _ -> failwith "Typechecker problem"
            )
        )
      | This -> Hashtbl.find lenv "this"
      | New cn ->
        let o = get_class cn in
        let fields = Hashtbl.create 16 in
        let app o = 
          List.iter (fun (att, _, _, _) -> Hashtbl.add fields att Null) o.attributes;
          None
        in
        let _ = ascendent_fold app o in
        VObj ({cls = o.class_name; fields = fields; f_fields = Hashtbl.create 16 })
        
      | NewCstr (cn, el) -> 
        let o = get_class cn in
        let fields = Hashtbl.create 16 in
        let app o = 
          List.iter (fun (att, _, _, final) -> if not final then Hashtbl.add fields att Null) o.attributes;
          None
        in
        let _ = ascendent_fold app o in
        let obj = {cls=o.class_name; fields=fields; f_fields = Hashtbl.create 16} in
        eval_call "constructor" obj (List.map (fun e -> eval e) el);
        VObj obj
      | MethCall (Get (Var class_name), meth_name, el) when List.exists (fun c_def -> c_def.class_name = class_name) p.classes ->
        (
          try 
          eval_call_s meth_name class_name (List.map (fun e -> eval e) el);
          Null
          with Return v -> v)
      | MethCall (e, s, el) -> 
        (try 
          eval_call s (evalo e) (List.map (fun e -> eval e) el);
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
        (*Verify if the class associated to obj, is a subclass of c*)
        let app o = 
          if o.class_name = c then Some true
          else None
        in

        (match ascendent_fold app (get_class obj.cls) with 
          None -> VBool false
          | _ -> VBool true
        )
      | Binop(Instanceof, _, _) -> failwith "Typechecker problem"
      | Array li -> 
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
        let rec generat_arr li = 
          match li with 
          [] -> failwith "Parser problem" 
          | [Some e] ->             
            let dim = evali e in
            if dim = 0 then error "Array length can not be zero";
            VArr (Array.init dim (fun i -> default_value tho))
          | (Some e)::li -> 
            let dim = evali e in
            if dim = 0 then error "Array length can not be zero";
            VArr (Array.init dim (fun i -> generat_arr li))
          | _ -> NotInitialised
        in
        generat_arr li
 
    in
  
    let rec exec (i: instr): unit = match i with
      | Print e -> Printf.printf "%d\n" (evali e)
      | Expr(e) -> let _ = eval e in () 
      | Return(e) -> raise (Return (eval e))

      | Set(mem_acc, e) ->
        (*
          à refaire, déja on n'a pas de notion de shadowing
          replace est dangereuse, psq si l'occurence d'une variable n'existe pas dans fields, elle l'a rajoute, ce qui justifie le 
            fonctionnement de tests
        *)
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
              else Hashtbl.add c_env.f_attributs s (eval e)

          | Field(eo, s) -> 
            (* à ce point pas besoin de vérifier que e d'évalue en objet*)
            let obj = evalo eo in 
            if Hashtbl.mem obj.fields s then Hashtbl.replace obj.fields s (eval e)
            else if Hashtbl.mem obj.f_fields s then error ("Immuable attribute " ^ s ^ " can not be modified.")
            else Hashtbl.add obj.f_fields s (eval e)  
          
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

    and exec_seq s = 
      List.iter exec s
    in

    exec_seq s)
  in
  
  exec_seq p.main (Hashtbl.create 1)



// | STATIC PRIVATE tho=typ id=IDENT LPAR params=params RPAR BEGIN
//   locals=list(var_decl)
//   code=list(instruction)
//  END { create_meth_object true id Private code params (flatten_list locals) tho }

// | STATIC PROTECTED tho=typ id=IDENT LPAR params=params RPAR BEGIN
// locals=list(var_decl)
// code=list(instruction)
// END { create_meth_object true id Protected code params (flatten_list locals) tho }

// | PRIVATE STATIC tho=typ id=IDENT LPAR params=params RPAR BEGIN
//   locals=list(var_decl)
//   code=list(instruction)
//  END { create_meth_object true id Private code params (flatten_list locals) tho }

// | PROTECTED STATIC tho=typ id=IDENT LPAR params=params RPAR BEGIN
// locals=list(var_decl)
// code=list(instruction)
// END { create_meth_object true id Protected code params (flatten_list locals) tho }

// | STATIC tho=typ id=IDENT LPAR params=params RPAR BEGIN
// locals=list(var_decl)
// code=list(instruction)
// END { create_meth_object true id PackagePrivate code params (flatten_list locals) tho }

// | PRIVATE tho=typ id=IDENT LPAR params=params RPAR BEGIN
//   locals=list(var_decl)
//   code=list(instruction)
//  END { create_meth_object false id Private code params (flatten_list locals) tho}

// | PROTECTED tho=typ id=IDENT LPAR params=params RPAR BEGIN
//   locals=list(var_decl)
//   code=list(instruction)
//  END { create_meth_object false id Protected code params (flatten_list locals) tho}

// | tho=typ id=IDENT LPAR params=params RPAR BEGIN
//   locals=list(var_decl)
//   code=list(instruction)
//  END { create_meth_object false id PackagePrivate code params (flatten_list locals) tho}
