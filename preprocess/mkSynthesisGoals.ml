open ParseSyntax
open Extensions

let var_sort_of_predicate_def (predicate_def:predicateDef) =
  let sort_list = predicate_def.args
                 |> List.filter (fun (arg:predicateArg) -> not arg.is_param)
                 |> List.map (fun (arg:predicateArg) -> arg.sort)
  in
  (assert (sort_list <> []));
  let arg_sort, ret_sort = List.split_tail sort_list in
  let ret_sort = Hfl.cast2baseSort ret_sort in
  `FunS (arg_sort, ret_sort)

  
let rec g path_env goal_map = function
  |QualifierDef _ :: other |PredicateDef _ :: other
   |DataDef _ :: other |MeasureDef _ :: other |RefinePredicateDef _ :: other ->
    g  path_env goal_map other

  |VarSpecDec (var_name, predicate_def) :: other ->
    let var_sort = var_sort_of_predicate_def predicate_def in
    let var_sort = (var_sort:> Hfl.sort) in
      let path_env' = PathEnv.add_bind
                        var_name
                        var_sort
                        path_env
      in
      let goal_map' = M.add var_name (path_env, var_sort) goal_map in
      g  path_env' goal_map' other
      
  |Goal var_name :: other ->
    (match M.find_opt var_name goal_map with
    |Some (var_path_env, var_sort) ->
      (var_name, (var_path_env, var_sort))::(g path_env goal_map other)
    |None ->
      invalid_arg (Printf.sprintf "goal %s has no specification"
                                  (Id.to_string_readable var_name))
    )

  |[] -> []


let measure_conditioin_of_sclar_constructor data_env (`DataS data) cons_name =
  let measure_constraint =
    DataType.Env.measure_constraint_of_constructor
      data_env
      (`DataS data)
      cons_name
  in
  measure_constraint.body
  |>
    BaseLogic.substitution
      (M.singleton
         Id.valueVar_id
         (BaseLogic.Cons (BaseLogic.DataS (data,[]), cons_name, [])))
   
      
let f data_env sort_env t =
  (* コンストラクタをbind *)
  let path_env =
    DataType.Env.fold_datatype
      (fun _ (def:DataType.definition) acc->
        List.map (fun (c:DataType.constructor) -> c.name) def.constructors
        |>
          List.fold_left
          (fun acc cons_name ->
            match M.find_opt cons_name sort_env with
            |Some `DataS data -> (* sclarなあたいはmeasure条件をplus *)
              let measure_cond  =
                measure_conditioin_of_sclar_constructor data_env (`DataS data) cons_name
              in
              acc
              |> PathEnv.add_bind cons_name (`DataS data)
              |> PathEnv.add_condition (`Base measure_cond)
            |Some cons_sort ->
              PathEnv.add_bind cons_name cons_sort acc
            |None -> assert false)
          acc
      )
      data_env
      PathEnv.empty
  in
  g path_env M.empty t
  


       
   
