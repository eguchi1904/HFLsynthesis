include Formula
      
(* let is_valid (t:t) = *)
(*   let z3_exp, _ = UseZ3.convert t in *)
(*   UseZ3.is_valid z3_exp *)


(* let to_z3_expr t = UseZ3.convert t *)

let fresh env i =
  match M.find_opt i env with
  |Some i' -> i' |None ->i                 

let rec replace_map (env:Id.t M.t) e =
  match e with
  |Bool _ | Int _ as e' -> e'
  |Set (s, es) -> Set (s, List.map (replace_map env) es)
  |Var (s, i) -> Var (s, fresh env i)
  |Unknown _ -> assert false
  |Cons (s, i, es) ->
    Cons (s, fresh env i, List.map (replace_map env) es)
  |UF (s, i, es) ->
    UF (s, fresh env i, List.map (replace_map env) es)
  |If (e1, e2, e3) ->
    If (replace_map env e1, replace_map env e2, replace_map env e3)
  |Times (e1, e2) ->
    Times (replace_map env e1, replace_map env e2)
  |Plus(e1, e2) ->
    Plus(replace_map env e1, replace_map env e2)
  |Minus (e1, e2) ->
    Minus (replace_map env e1, replace_map env e2)
  |Eq (e1, e2) ->
    Eq (replace_map env e1, replace_map env e2)
  |Neq (e1, e2) ->
    Neq (replace_map env e1, replace_map env e2)
  |Lt (e1, e2) ->
    Lt (replace_map env e1, replace_map env e2)
  |Le (e1, e2) ->
    Le (replace_map env e1, replace_map env e2)
  |Gt (e1, e2) ->
    Gt (replace_map env e1, replace_map env e2)
  |Ge (e1, e2) ->
    Ge (replace_map env e1, replace_map env e2)
  |And (e1, e2) ->
    And (replace_map env e1, replace_map env e2)
  |Or (e1, e2) ->
    Or (replace_map env e1, replace_map env e2)
  |Implies (e1, e2) ->
    Implies (replace_map env e1, replace_map env e2)
  |Iff (e1, e2) ->
    Iff (replace_map env e1, replace_map env e2)
  |Member (e1, e2) ->
    Member (replace_map env e1, replace_map env e2)
  |Union (e1, e2) ->
    Union (replace_map env e1, replace_map env e2)
  |Intersect (e1, e2) ->
    Intersect (replace_map env e1, replace_map env e2)
  |Diff (e1, e2) ->
    Diff (replace_map env e1, replace_map env e2)
  |Subset (e1, e2) ->
    Subset (replace_map env e1, replace_map env e2)
  |Neg e1 -> Neg (replace_map env e1)
  |Not e1 -> Not (replace_map env e1)
  |All _ | Exist _ -> assert false
