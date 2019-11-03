open ParseSyntax
open Extensions

let rec g_clause_abs refine_id_set (`Abs (args, body)) =
  `Abs(args, g_clause refine_id_set body)
  
and g_clause refine_id_set (c:clause) =
  match c with
  | `Base e -> `Base e
  | `App {head = head; args = cs } ->
     let cs' = List.map (g_clause refine_id_set) cs in
     if S.mem head refine_id_set then
       let params, c = List.split_tail cs' in
       let params = List.map (function `Abs _ as abs -> abs |_ -> assert false) params in
       `RData (head, params, c)
     else
       `App {head = head; args = cs'}
  | `RData _ -> assert false
  | `Or (c1, c2) -> `Or (g_clause refine_id_set c1, g_clause refine_id_set c2)
  | `And (c1, c2) -> `And (g_clause refine_id_set c1, g_clause refine_id_set c2)
  | `Abs _ as abs_clause -> g_clause_abs refine_id_set abs_clause


let g_refine_case refine_id_set (case:refineCase) =
  {name = case.name;
   args = case.args;
   body = g_clause refine_id_set case.body}

let g_predicate_def refine_id_set {name = name;
                                   args = args;
                                   fixpoint = fixpoint;
                                   body = body
                                  }
  =
  let body' =
    match body with
    |Some c1, c2 ->
      let c1' = g_clause refine_id_set c1 in
      let c2' = g_clause refine_id_set c2 in
      Some c1', c2'
    |None, c2 ->
      let c2' = g_clause refine_id_set c2 in
      None, c2'
  in
  {name = name;
   args = args;
   fixpoint = fixpoint;
   body = body'
  }

  
let rec g refine_id_set = function
  |(QualifierDef _ as elm):: other |(Goal _ as elm) :: other
   |(DataDef _ as elm) :: other |(MeasureDef _ as elm) :: other ->
    elm::(g refine_id_set other)

  |RefinePredicateDef {name = name;
                       param = predicate_args;
                       cases = cases}:: other ->
    let refine_id_set' = S.add name refine_id_set in
    let elm' = RefinePredicateDef {name = name;
                                   param = predicate_args;
                                   cases = List.map (g_refine_case refine_id_set') cases}
    in
    elm' :: (g refine_id_set' other)

  |PredicateDef predicate_def :: other ->
    let predicate_def' = g_predicate_def refine_id_set predicate_def in
    PredicateDef predicate_def' :: (g refine_id_set other)

  |VarSpecDec (var_name, predicate_def) :: other ->
    let predicate_def' = g_predicate_def refine_id_set predicate_def in
    VarSpecDec (var_name, predicate_def') :: (g refine_id_set other)

  |[] -> []

let f t = g S.empty t
    
      

  
