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

  
let rec g path_env = function
  |QualifierDef _ :: other |PredicateDef _ :: other
   |DataDef _ :: other |MeasureDef _ :: other |RefinePredicateDef _ :: other ->
    g  path_env other

  |VarSpecDec (var_name, predicate_def) :: other ->
    let var_sort = var_sort_of_predicate_def predicate_def in
      let path_env' = PathEnv.add_bind
                        var_name
                        var_sort
                        path_env
      in
      g  path_env' other
      
  |Goal var_name :: other ->
    (var_name, path_env)::(g path_env other)

  |[] -> []
    
   
      
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
            |Some cons_sort ->
              PathEnv.add_bind cons_name cons_sort acc
            |None -> assert false)
          acc
      )
      data_env
      PathEnv.empty
  in
  g path_env t
  


       
   
