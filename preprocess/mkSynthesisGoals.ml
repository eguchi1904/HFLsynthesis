open ParseSyntax
open Extensions

let rec g (sort_env:Hfl.sort M.t) path_env = function
  |QualifierDef _ :: other |PredicateDef _ :: other
   |DataDef _ :: other |MeasureDef _ :: other |RefinePredicateDef _ :: other ->
    g sort_env path_env other

  |VarSpecDec (var_name, _) :: other ->
    (match M.find_opt var_name sort_env with
    |Some (`FunS (sort_list, `BoolS)) ->
      assert (sort_list <> []);
      let arg_sorts, ret_sort = List.split_tail sort_list in
      let ret_sort = Hfl.cast2baseSort ret_sort in
      let var_sort =
        if arg_sorts = [] then
          ret_sort
        else
          `FunS (arg_sorts, ret_sort)
      in
      
      let path_env' = PathEnv.add_bind
                        var_name
                        var_sort
                        path_env
      in
      g sort_env path_env' other
      
    |_ -> assert false)

  |Goal var_name :: other ->
    (var_name, path_env)::(g sort_env path_env other)

  |[] -> []
    
   
      
let f data_env sort_env t =
  (* コンストラクタをbind *)
  let path_env =
    DataType.Env.fold_datatype
      (fun data (def:DataType.definition) acc->
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
  g sort_env path_env t
  


       
   
