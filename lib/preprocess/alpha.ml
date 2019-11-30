open ParseSyntax

let unbound_id i = Id.to_string_readable i |>Id.genid_const

let fresh env i =
  match M.find_opt i env with
  |Some i' -> i' |None ->assert false

   
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

                    
let rec g_clause_abs env (`Abs (args, body)) :abstClause=
  let old_arg_id = List.map fst args in
  let new_args =  List.map (fun (i, sort) -> (newid i, sort)) args in
  let new_arg_id = List.map fst new_args in
  let env' = M.add_list2 old_arg_id new_arg_id env in
  `Abs (new_args, g_clause env' body)
  
and g_clause env clause =
  match clause with
  | `Abs _ as abs_clause -> (g_clause_abs env abs_clause:>clause)
  | `Base base -> `Base (g_base env base)
  | `App {head = head; args = args} ->
     let head' = fresh env head in
     `App {head = head';
           args = List.map (g_clause env) args}
  | `RData (name, params, c) ->
     let name' = fresh env name in
     `RData (name',
             List.map (g_clause_abs env) params,
             g_clause env c)
  | `Or (c1, c2) -> `Or ((g_clause env c1), (g_clause env c2))
  | `And (c1, c2) -> `And ((g_clause env c1), (g_clause env c2))


let g_qualifier env qualifier =
  let (args, body) = Qualifier.reveal qualifier in
  let old_arg_id = List.map fst args in
  let new_args =  List.map (fun (i, sort) -> (newid i, sort)) args in
  let new_arg_id = List.map fst new_args in
  let env' = M.add_list2 old_arg_id new_arg_id env in
  let body' = g_base env' body in
  Qualifier.make new_args body'


(* constructorのidの付け替え、 *)
let g_typedef env {name = name; constructors = constructor_list } =
  let env', constructor_list' =
    List.fold_right
      (fun (cons:constructor) (acc_env', acc_cons_list) ->
        let new_name = newid cons.name in
        (M.add cons.name new_name acc_env',
         {name = new_name; args = cons.args}::acc_cons_list))
      constructor_list
      (env, [])
  in
  {name = name; constructors = constructor_list'}, env'



let g_measure_case
      env
      ({constructor = cons; args = args ; body =  body}:formulaCase)
  =
  let cons' = fresh env cons in
  let new_args = List.map newid args in
  let env' = M.add_list2 args new_args env in
  let body' = g_base env' body in
 {constructor = cons'; args = new_args ; body =  body'}  

  
  
  

let g_measure env {name = name;
                   termination = terminaion;
                   inputSort = `DataS data;
                   returnSort = out_sort;
                   matchCases = cases}   =
  let name' = newid name in
  let env' = M.add name name' env in (* measure名をfresh *)
  let cases' = List.map (g_measure_case env') cases in
  {name = name';
   termination = terminaion;
   inputSort = `DataS data;
   returnSort = out_sort;
   matchCases = cases'},
  env'

let g_refine_case env
                  ({name = cons; args = args; body = body}:refineCase) =
  let cons' = fresh env cons in
  let new_args = List.map newid args in
  let env' = M.add_list2 args new_args env in
  let body' = g_clause env' body in
  {name = cons'; args = new_args; body = body'}
  

let g_refine env {name = name;
                  param = predicate_args;
                  cases = cases}
  =
  let name' = newid name in
  let env' = M.add name name' env in (* measure名をfresh *)
  let predicate_args' =
    List.map
      (fun (predicate_arg:predicateArg) ->
        {name = newid predicate_arg.name;
         is_param = predicate_arg.is_param;
         sort = predicate_arg.sort})
      predicate_args
  in
  let env'' =
    M.add_list2
      (List.map (fun (x:predicateArg) -> x.name) predicate_args)
      (List.map (fun (x:predicateArg) -> x.name) predicate_args')    
      env'
  in
  let cases' = List.map (g_refine_case env'') cases in
  {name = name';
   param = predicate_args';
   cases = cases'},
  env'                          (* measure名の対応を加えたenv *)
    

let g_predicate_def env ({name = name;
                         args = predicate_args;
                         fixpoint = fixpoint_opt;
                         body = body}
                         :predicateDef) =
  
  let name' = newid name in
  let env' = M.add name name' env in (*predicate名をfresh *)
  let predicate_args' =
    List.map
      (fun (predicate_arg:predicateArg) ->
        {name = newid predicate_arg.name;
         is_param = predicate_arg.is_param;
         sort = predicate_arg.sort})
      predicate_args
  in
  let env'' =
    M.add_list2
      (List.map (fun (x:predicateArg) -> x.name) predicate_args)
      (List.map (fun (x:predicateArg) -> x.name) predicate_args')    
      (match fixpoint_opt with None -> env |Some _ -> env')
  in
  let body' = (match body with
               |Some c1, c2 -> Some (g_clause env'' c1), g_clause env'' c2
               |None, c2 -> None, g_clause env'' c2)
  in
  {name = name';
   args = predicate_args';
   fixpoint = fixpoint_opt;
   body = body'},
  env'
  
let rec g env = function
  |QualifierDef qualifiers :: other ->
    QualifierDef (List.map (g_qualifier env) qualifiers) :: g env other

  |DataDef typedef :: other ->
    let typedef', env' = g_typedef env typedef in
    DataDef typedef' :: g env' other

  |MeasureDef measure :: other ->
    let measure', env' = g_measure env measure in
    MeasureDef measure' :: g env' other

  |RefinePredicateDef refine :: other ->
    let refine', env' = g_refine env refine in
    RefinePredicateDef refine' :: g env' other

  |PredicateDef predicate_def :: other ->
    let predicate_def', env' = g_predicate_def env predicate_def in
    PredicateDef predicate_def' :: g env' other

  (* var_nameはそのまま *)
  |VarSpecDec (var_name, predicate_def) :: other ->
    let predicate_def', env' = g_predicate_def env predicate_def in
    VarSpecDec (var_name, predicate_def') :: g env' other

  |Goal var_name :: other -> Goal var_name :: g env other

  |[] -> []
    
          
  
let f t = g M.empty t

                
