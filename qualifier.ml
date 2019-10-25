type t = (Id.t * Hfl.baseSort) list * BaseLogic.t

let rec enumerate_possible_args
      penv ~must_include_vars ~used_vars must_include_var_is_used args_formal =
  match args_formal with
  |[] -> []
  |[(_, sort)] when must_include_var_is_used ->
    let HeadCandidates.{scalar = scl_vars;_} = PathEnv.find_heads sort penv in
    let scl_vars = List.map fst scl_vars
                   |> List.filter (fun v -> not (S.mem v used_vars))
    in
    [scl_vars]
  |[(_, sort)] ->
    let HeadCandidates.{scalar = scl_vars;_} = PathEnv.find_heads sort penv in
    let scl_vars = List.map fst scl_vars
                   |> List.filter (fun v -> S.mem v must_include_vars && not (S.mem v used_vars))
    in
    [scl_vars]
  |(_, sort)::other_args ->
    let HeadCandidates.{scalar = scl_vars;_} = PathEnv.find_heads sort penv in
    let scl_vars = List.map fst scl_vars
                   |> List.filter (fun v -> not (S.mem v used_vars))
    in
    List.map
      (fun v ->
        let used_vars = (S.add v used_vars) in
        let must_include_var_is_used = must_include_var_is_used || S.mem v must_include_vars in
        (enumerate_possible_args
           penv
           ~must_include_vars ~used_vars must_include_var_is_used
           other_args)
      |> List.map (fun other_possible_args -> v::other_possible_args)
      )
      scl_vars
    |>
      List.concat
    
    
    


let gen_formula penv ~must_include_vars ((args, body):t) =
  let possible_arg_vars =
    enumerate_possible_args
      penv
      ~must_include_vars ~used_vars:S.empty false
      args
  in
  let open BaseLogic in
  List.map
    (fun real_args ->
      let subst = 
        List.fold_left2
          (fun acc real (formal, sort) ->
            M.add formal (Var ((Hfl.to_baseLogic_sort sort), real)) acc)
          M.empty
          real_args
          args
      in
      BaseLogic.substitution subst body
    )
  possible_arg_vars
      

  

module Env:sig
  
  
end
