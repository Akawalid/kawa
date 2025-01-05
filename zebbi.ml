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