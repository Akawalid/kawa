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
    | Get (m) -> type_mem_access m tenv
    | MethCall (e, s, le) -> failwith "RAMY"
    | This -> TVoid
    | New (s) -> type_constructor s None
    | NewCstr(s, le) -> type_constructor s (Some le)

  and type_constructor s le = 
    try 
      let o = List.find (fun o -> o.class_name = s) p.classes in
      match le with 
        None -> TClass s
      | Some le -> 
        let _ = type_method "constructor" le o in
        TClass s
    with Not_found -> error ("Missing declaration of the class " ^ s)

  and type_method s le o =
    let rec loop le ltypes = 
      match le, ltypes with 
      [], [] -> ()
      | e::le, (_, tho)::ltypes ->
        let tho' = type_expr e tenv in
        if not (subtype tho' tho) then type_error tho' tho
        ;loop le ltypes
      | _ -> error ("No method " ^ s ^ " found.")
    in
    try 
      let o = List.find (fun obj -> obj.method_name = s) o.methods in 
      loop le o.params
    with Not_found -> error ("Missing declaration of the method " ^ s)

  and subtype tho' tho =
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

  and type_mem_access m tenv = 
    match m with
     Var s -> 
      (
      try Env.find s tenv
      with Not_found -> error ("Missing declaration of the variabel " ^ s)
      ) 
    | Field (e, s) -> 
        let tho_e = type_expr e tenv in
        (match tho_e with 
          TClass c -> 
            (
            try 
              let o = List.find (fun o -> o.class_name = c) p.classes in
              let _, tho = List.find (fun (s', tho) -> s' = s) o.attributes in
              tho  
            with Not_found -> error (c ^ " has no attribute name: " ^ s)
            )
          | _ -> error ("")
        )
  in

  let rec check_instr i ret tenv = match i with
    | Print e -> check e TInt tenv
    | _ -> failwith "case not implemented in check_instr"
  and check_seq s ret tenv =
    List.iter (fun i -> check_instr i ret tenv) s
  in

  check_seq p.main TVoid tenv
