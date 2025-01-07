open Kawa

type value =
  | VInt  of int
  | VBool of bool
  | VObj  of obj
  | Null
and obj = {
  cls:    string;
  fields: (string, value) Hashtbl.t;
}

exception Error of string
exception Return of value

let exec_prog (p: program): unit =
  let env = Hashtbl.create 16 in
  List.iter (fun (x, _) -> Hashtbl.add env x Null) p.globals;

  let get_class c = 
    List.find (fun obj -> obj.class_name = c) p.classes
  in
  let rec ascendent_fold application o =
    let res = application o in
    if res <> None then res
    else 
      match o.parent with 
       None -> application o
      | Some c -> ascendent_fold application (get_class c)
    in

  (*On crée un environement qui contiendra les noms des classes comme clés et les attributs statiques comme valeurs*)
  
  
  let create_class_env = 
    let get_all_class_attributs c_def = 
      let fields = Hashtbl.create 16 in
      let app o = 
        List.iter (fun (n_att, _, _) -> Hashtbl.add fields n_att Null) c_def.s_attributs;
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
        (get_all_class_attributs c_def)
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
          | Field (Get (Var c), s) when List.exists (fun c_def -> c_def.class_name = c) p.classes ->
            (* (get_class p.classes c) *)
            Hashtbl.find (Hashtbl.find class_env c) s;
          | Field(eo, att) -> 
            let obj = evalo eo in
            Hashtbl.find obj.fields att  
        )
      | This -> Hashtbl.find lenv "this"
      | New cn -> 
        let o = get_class cn in
        let fields = Hashtbl.create 16 in
        let app o = 
          List.iter (fun (att, _, _) -> Hashtbl.add fields att Null) o.attributes;
          None
        in
        let _ = ascendent_fold app o in
        VObj ({cls = o.class_name; fields = fields})
        
      | NewCstr (cn, el) -> 
        let o = get_class cn in
        let fields = Hashtbl.create 16 in
        let app o = 
          List.iter (fun (att, _, _) -> Hashtbl.add fields att Null) o.attributes;
          None
        in
        let _ = ascendent_fold app o in
        eval_call "constructor" {cls=o.class_name; fields=fields} (List.map (fun e -> eval e) el);
        VObj ({cls=o.class_name; fields=fields})
      | MethCall (Get (Var c), s, el) when List.exists (fun c_def -> c_def.class_name = c) p.classes ->
        (* (get_class p.classes c) *)
        (try 
          eval_call_s s c (List.map (fun e -> eval e) el);
          Null
          with Return v -> v
        )
      | MethCall (e, s, el) -> 
        (try 
          eval_call s (evalo e) (List.map (fun e -> eval e) el);
          Null
        with Return v -> v
        )
        
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
            if(Hashtbl.mem lenv s) then Hashtbl.replace lenv s ve
            else if Hashtbl.mem env s then  Hashtbl.replace env s ve 
            else failwith "Typechecker problem"
          | Field (Get (Var c), s) when List.exists (fun c_def -> c_def.class_name = c) p.classes ->
              Hashtbl.replace (Hashtbl.find class_env c) s (eval e);
          | Field(eo, s) -> 
            (* à ce point pas besoin de vérifier que e d'évalue en objet*)
            let obj = evalo eo in 
            Hashtbl.replace obj.fields s (eval e) 
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