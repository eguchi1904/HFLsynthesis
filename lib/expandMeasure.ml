


let rec g e =
let open BaseLogic   in
  match e with
  |UF (_, measure_id, [Cons ((DataS (data_s,[])), cons_name, es)]) ->
    (match DataType.Env.find_measure_case
            (!DataType.Env.global_ref)
            (`DataS data_s)
            measure_id
            cons_name
    with
      None -> assert false
     |Some {args = args ; body = case_body;_ } ->
       (assert (List.length args = List.length es) );
       let sita = List.fold_left2
                    (fun sita (id,_) e -> M.add id e sita)
                    M.empty
                    args es
       in
       let case_body' = BaseLogic.substitution sita case_body in
       g case_body'
    )
  |UF (s, i, es) ->
    UF (s, i, List.map g es)
  |Cons (s, i, es) ->
    Cons (s,  i, List.map g es)
  |Bool _ | Int _ as e' -> e'
  |Set (s, es) -> Set (s, List.map g es)
  |Var (s, i) -> Var (s, i)
  |Unknown _ -> assert false
  |If (e1, e2, e3) ->
    If (g e1, g e2, g e3)
  |Times (e1, e2) ->
    Times (g e1, g e2)
  |Plus(e1, e2) ->
    Plus(g e1, g e2)
  |Minus (e1, e2) ->
    Minus (g e1, g e2)
  |Eq (e1, e2) ->
    Eq (g e1, g e2)
  |Neq (e1, e2) ->
    Neq (g e1, g e2)
  |Lt (e1, e2) ->
    Lt (g e1, g e2)
  |Le (e1, e2) ->
    Le (g e1, g e2)
  |Gt (e1, e2) ->
    Gt (g e1, g e2)
  |Ge (e1, e2) ->
    Ge (g e1, g e2)
  |And (e1, e2) ->
    And (g e1, g e2)
  |Or (e1, e2) ->
    Or (g e1, g e2)
  |Implies (e1, e2) ->
    Implies (g e1, g e2)
  |Iff (e1, e2) ->
    Iff (g e1, g e2)
  |Member (e1, e2) ->
    Member (g e1, g e2)
  |Union (e1, e2) ->
    Union (g e1, g e2)
  |Intersect (e1, e2) ->
    Intersect (g e1, g e2)
  |Diff (e1, e2) ->
    Diff (g e1, g e2)
  |Subset (e1, e2) ->
    Subset (g e1, g e2)
  |Neg e1 -> Neg (g e1)
  |Not e1 -> Not (g e1)
  |All _ | Exist _ -> assert false

open Hfl
let rec f = function
  | `Base base -> `Base (g base)
  | `App {head = head; params = params; args = cs} ->
     `App {head = head; params = params; args = List.map f cs}
  | `Or (c1, c2) -> `Or (f c1, f c2)
  | `And (c1, c2) -> `And (f c1, f c2)
  | _ -> assert false


