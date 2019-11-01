open ParseSyntax

let unbound_id i = Id.to_string_readable i |>Id.genid_const

let fresh env i =
  match M.find_opt i env with
  |Some i' -> i' |None ->unbound_id i  
   
let rec g_base (env:Id.t M.t) e =
  let open BaseLogic in
  match e with
  |Bool _ | Int _ as e' -> e'
  |Set (s, es) -> Set (s, List.map (g_base env) es)
  |Var (s, i) -> Var (s, fresh env i)
  |Unknown _ -> assert false
  |Cons (s, i, es) ->
    Cons (s, fresh env i, List.map (g_base env) es)
  |UF (s, i, es) ->
    UF (s, fresh env i, List.map (g_base env) es)
  |If (e1, e2, e3) ->
    If (g_base env e1, g_base env e2, g_base env e3)
  |Times (e1, e2) ->
    Times (g_base env e1, g_base env e2)
  |Plus(e1, e2) ->
    Plus(g_base env e1, g_base env e2)
  |Minus (e1, e2) ->
    Minus (g_base env e1, g_base env e2)
  |Eq (e1, e2) ->
    Eq (g_base env e1, g_base env e2)
  |Neq (e1, e2) ->
    Neq (g_base env e1, g_base env e2)
  |Lt (e1, e2) ->
    Lt (g_base env e1, g_base env e2)
  |Le (e1, e2) ->
    Le (g_base env e1, g_base env e2)
  |Gt (e1, e2) ->
    Gt (g_base env e1, g_base env e2)
  |Ge (e1, e2) ->
    Ge (g_base env e1, g_base env e2)
  |And (e1, e2) ->
    And (g_base env e1, g_base env e2)
  |Or (e1, e2) ->
    Or (g_base env e1, g_base env e2)
  |Implies (e1, e2) ->
    Implies (g_base env e1, g_base env e2)
  |Iff (e1, e2) ->
    Iff (g_base env e1, g_base env e2)
  |Member (e1, e2) ->
    Member (g_base env e1, g_base env e2)
  |Union (e1, e2) ->
    Union (g_base env e1, g_base env e2)
  |Intersect (e1, e2) ->
    Intersect (g_base env e1, g_base env e2)
  |Diff (e1, e2) ->
    Diff (g_base env e1, g_base env e2)
  |Subset (e1, e2) ->
    Subset (g_base env e1, g_base env e2)
  |Neg e1 -> Neg (g_base env e1)
  |Not e1 -> Not (g_base env e1)
  |All _ | Exist _ -> assert false

                    
let rec g_clause_abs env (`Abs (args, body)) =
  let old_arg_id = List.map fst args in
  let new_arg_id = List
   
   
    
                
