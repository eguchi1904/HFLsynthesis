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

let newid id =
  Id.to_string_readable id |> Id.genid_const

                    
let rec g_clause_abs env (`Abs (args, body)) :Hfl.abstClause=
  let old_arg_id = List.map fst args in
  let new_args =  List.map (fun (i, sort) -> (newid i, sort)) args in
  let new_arg_id = List.map fst new_args in
  let env' = M.add_list2 old_arg_id new_arg_id env in
  `Abs (new_args, g_clause env' body)
  
and g_clause env clause =
  match clause with
  | `Abs _ as abs_clause -> (g_clause_abs env abs_clause:> Hfl.clause)
  | `Base base -> `Base (g_base env base)
  | `App Hfl.{head = head; params = params; args = args} ->
     let head' = fresh env head in
     `App Hfl.{head = head';
               params = List.map (g_clause_abs env) params;
               args = List.map (g_clause env) args}
  | `RData (name, params, c) ->
     let name' = fresh env name in
     `RData (name',
             List.map (g_clause_abs env) params,
             g_clause env c)
  | `Or (c1, c2) -> `Or ((g_clause env c1), (g_clause env c2))
  | `And (c1, c2) -> `And ((g_clause env c1), (g_clause env c2))                    


                
