open ParseSyntax

let separete_params_from_application_args
    :predicateArg list -> Hfl.clause list -> Hfl.abstClause list * Hfl.clause list = 
  (fun predicate_args cs ->
  (assert (List.length predicate_args  = List.length cs));
  List.fold_right2
    (fun predicate_arg clause (acc_param, acc_arg) ->
      if predicate_arg.is_param then
        match clause with
        | `Abs _ as abs_clause -> (abs_clause::acc_param, acc_arg)
        | _ -> assert false
      else
        (acc_param, clause::acc_arg)
    )
    predicate_args
    cs
    ([], [])
  )


let rec to_hfl_clause_abs pmap  (`Abs (args, c)) =  `Abs (args, to_hfl_clause pmap c)
  
and to_hfl_clause:predicateDef M.t -> clause -> Hfl.clause =
  (fun pmap c ->
    match c with
    | `Abs _ as abs_c -> (to_hfl_clause_abs pmap abs_c:>Hfl.clause)
    | `Base base -> `Base base
    | `App {head = head; args = cs} ->
       let hfl_cs = List.map (to_hfl_clause pmap) cs in
       (match M.find_opt head pmap with
        |Some head_def ->
          let params, args =
            separete_params_from_application_args
              head_def.args
              hfl_cs
          in
          `App {head = head; params = params; args = args}
        |None -> assert false)
  
    | `RData (id, abst_cs, c) ->
       `RData (id,
               List.map (to_hfl_clause_abs pmap) abst_cs,
               to_hfl_clause pmap c)

    | `Or (c1, c2) ->
       `Or (to_hfl_clause pmap c1,
            to_hfl_clause pmap c2)

    | `And (c1, c2) ->
       `And (to_hfl_clause pmap c1,
            to_hfl_clause pmap c2)
  )
          
          

let separate_params: predicateArg list -> (Id.t * Hfl.abstSort) list * (Id.t * Hfl.sort) list =
  (fun predicate_args -> assert false)

let align_by_arg: Id.t list -> Hfl.clause -> Hfl.clause list =
  (fun args clause -> assert false)
   

let mk_fhorn (pmap: predicateDef M.t) (predicate_def:predicateDef) :Hfl.fhorn=
  let params, args = separate_params predicate_def.args in  
  match predicate_def.body with
  |(Some c1, c2) ->
    let c1 = to_hfl_clause pmap c1 in
    let c2 = to_hfl_clause pmap c2 in
    let arg_cs = align_by_arg (List.map fst args) c1 in
    {params = params;
     args = args;
     body = `Horn (arg_cs, c2)}
  |None, c2 ->
    let c2 = to_hfl_clause pmap c2 in
    {params = params;
     args = args;
     body = `Horn ([], c2)}    
    
  

(* let g ep t = *)
(*   match t with *)
(*   |(PredicateDef predicate_def ) :: other -> *)
    
