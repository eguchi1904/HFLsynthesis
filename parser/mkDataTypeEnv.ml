open ParseSyntax


let mk_definition (typedef:typedef) other =
  let data = typedef.name in
  match List.find_opt 
          (function |MeasureDef (measure:DataType.measure)
                    when measure.inputSort = `DataS data
                     -> true
                    |_ -> false)
          other
  with
  |Some MeasureDef (measure:DataType.measure) ->
    let cons_args_id =
      List.map
        (fun (case:DataType.formulaCase) -> (case.constructor, case.args))
        measure.matchCases
    in
    let dataType_cons_list =
      List.map
        (fun (cons:constructor) ->
          let arg_id = List.assoc cons.name cons_args_id in (* 参考id名を取得 *)
          let arg_id = List.map (fun id -> Id.to_string_readable id |> Id.genid_const) arg_id in
          assert (List.length arg_id = List.length cons.args);
          let args = List.combine arg_id cons.args in
          DataType.{name = cons.name;
                    args = args}
        )
        typedef.constructors
    in
    DataType.{name = data;
              constructors = dataType_cons_list}
  |None ->
    let dataType_cons_list =
      List.map
        (fun (cons:constructor) ->
          let args = List.map (fun arg_sort -> (Id.genid "x"), arg_sort) cons.args in
          DataType.{name = cons.name;
                    args = args}
        )
        typedef.constructors
    in
    DataType.{name = data;
              constructors = dataType_cons_list}

  |Some _ -> assert false


let mk_refine_case pmap sort_env ({name = cons; args = args; body = c}:refineCase) =
  if args = [] then
    DataType.{constructor = cons; args = [] }
  else
    let c = to_hfl_clause pmap c in  
    let arg_id_cs = align_by_arg args c|> List.combine args in
    match M.find cons sort_env with
    | `FunS (arg_sort, _) ->
       (assert (List.length arg_sort = List.length arg_id_cs));
       let args =
         List.map2
           (fun (a,b) c -> (a, c, b))
           arg_id_cs
           arg_sort
       in
       DataType.{constructor = cons;
                 args = args}
    | _ -> assert false
         
    
    
let mk_refine pmap sort_env ({name = name; param = predicate_args; cases = cases}:refinePredicate) =
  let param:(Id.t * Hfl.abstSort) list =
    List.map
      (fun (arg:predicateArg) ->
        match arg.sort with
        | `FunS (_, `BoolS) as abst_sort -> (arg.name, abst_sort)
        | _ -> assert false)
      predicate_args
  in
  let cases' = List.map (mk_refine_case  pmap sort_env) cases in
  DataType.{name = name;
            param = param;
            constructors = cases'}
  
  
                      
   
let rec g pmap sort_env data_env = function
  |QualifierDef _ :: other |Goal _ :: other |VarSpecDec _ :: other |PredicateDef _ :: other ->
    g pmap sort_env data_env other
  |DataDef typedef :: other ->
    let data_def = mk_definition typedef other in (* 引数のidを決定する *)
    let () = DataType.Env.add_definition data_env data_def in
    g pmap sort_env data_env other
  |MeasureDef (measure:DataType.measure) :: other ->
    let () = DataType.Env.add_measure data_env measure in
    g pmap sort_env data_env other
  |RefinePredicateDef refine_predicate :: other ->
    let refine = mk_refine pmap sort_env refine_predicate in
    let () = DataType.Env.add_refine data_env refine  in
    g pmap sort_env data_env other
  |[] -> data_env
    
    

let f pmap sort_env t =
  g pmap sort_env (DataType.Env.init ()) t
    
