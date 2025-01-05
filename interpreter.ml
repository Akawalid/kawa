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
  (* pour garder dans this la classe de l'objet courant*)
  let obj_courant = ref { cls = "MyClass"; fields = Hashtbl.create 0 } in
  
  let rec eval_call f this args =
    obj_courant := this;
    let c = List.find (fun class_d -> class_d.class_name = this.cls) p.classes in
    let meth = List.find (fun meth_d -> meth_d.method_name = f) c.methods in

    let lenv = Hashtbl.create 16 in
    (*ajout des parametre dans l'espace locale*)
    List.iter2 (fun (par, _) v  -> Hashtbl.add lenv par v) meth.params args;
    (*ajout des vars locals dans *)
    List.iter (fun (par, _) -> Hashtbl.add lenv par Null) meth.locals;
    exec_seq meth.code lenv;


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
          | Field(eo, att) -> 
            let obj = evalo eo in
            Hashtbl.find obj.fields att  
        )
      | This -> VObj !obj_courant
      | New cn -> 
        let c = List.find (fun class_d -> class_d.class_name = cn) p.classes in
        let fields = Hashtbl.create 16 in
        List.iter (fun (att,_) -> Hashtbl.add fields att Null) c.attributes;
        VObj ({cls=c.class_name; fields=fields})
        
      | NewCstr (cn, el) -> 
        let c = List.find (fun class_d -> class_d.class_name = cn) p.classes in
        let fields = Hashtbl.create 16 in
        List.iter (fun (att, _) -> Hashtbl.add fields att Null) c.attributes;

        eval_call "constructor" {cls=c.class_name; fields=fields} (List.map (fun e -> eval e) el);
        VObj ({cls=c.class_name; fields=fields})
        
      | MethCall (e, s, el) -> 
        (try 
          eval_call s (evalo e)(List.map (fun e -> eval e) el);
          Null
        with 
          |Return v -> v)
        
        | _ -> failwith "zebbi"
    in
  
    let rec exec (i: instr): unit = match i with
      | Print e -> Printf.printf "%d\n" (evali e)
      | Expr(e) -> let _ = eval e in () 
      | Return(e) -> raise (Return (eval e))

      | Set(mem_acc, e) ->
        let ve = eval e in
        (match mem_acc with 
          | Var s -> 
            if(Hashtbl.mem lenv s) then 
              Hashtbl.replace lenv s ve
            else
              Hashtbl.replace env s ve 
              
          |Field(eo,s) -> 
            (* à ce point pas besoin de vérifier que e d'évalue en objet*)
            let obj = evalo eo in 
            Hashtbl.replace obj.fields s (eval e) 
        )
      | If(e, s1, s2) -> 
        if(evalb e) then exec_seq s1
        else exec_seq s2

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
