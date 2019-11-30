type t = (Id.t * Hfl.baseSort) list * BaseLogic.t

let make args body = (args, body)

let to_string ((args, body):t) =
  let args_str = args
                 |> List.map
                      (fun (id, sort) ->
                        let sort = (sort:>Hfl.sort) in
                        (Id.to_string_readable id)^":"^(Hfl.sort2string sort))
                 |> String.concat ","
  in
  "fun "^args_str^" ->"^(BaseLogic.p2string body)        

let reveal (t:t) = t

let rec enumerate_possible_args
      penv ~must_include_vars ~used_vars must_include_var_is_used args_formal =
  match args_formal with
  |[] -> []
  |[(_, sort)] when must_include_var_is_used ->
    let HeadCandidates.{scalar = scl_vars;_} = PathEnv.find_heads sort penv in
    let scl_vars = List.map fst scl_vars
                   |> List.filter (fun v -> not (S.mem v used_vars))
    in
    List.map (fun var -> [var]) scl_vars
  |[(_, sort)] ->
    let HeadCandidates.{scalar = scl_vars;_} = PathEnv.find_heads sort penv in
    let scl_vars = List.map fst scl_vars
                   |> List.filter (fun v -> S.mem v must_include_vars && not (S.mem v used_vars))
    in
    List.map (fun var -> [var]) scl_vars    
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
    
    
    


let gen_formulas data_env penv ~must_include_vars ((args, body):t) =
  let possible_arg_vars =
    enumerate_possible_args
      penv
      ~must_include_vars ~used_vars:S.empty false
      args
  in
  (* let () = Printf.printf "args.len = %d\n" (List.length args) in *)
  (* let () = possible_arg_vars *)
  (*          |> List.map (List.map (Id.to_string_readable)) *)
  (*          |> List.map (String.concat ",") *)
  (*          |> List.map (fun s -> "("^s^")") *)
  (*          |> String.concat ";" *)
  (*          |> Printf.printf "\npsible_arg = [%s]\n" *)
  (* in *)
  let open BaseLogic in
  List.map
    (fun real_args ->
      let subst = 
        List.fold_left2
          (fun acc real (formal, sort) ->
            if DataType.Env.is_constructor data_env real then
              M.add formal (Cons ((Hfl.to_baseLogic_sort sort), real, [])) acc
            else
              M.add formal (Var ((Hfl.to_baseLogic_sort sort), real)) acc
          )
          M.empty
          real_args
          args
      in
      BaseLogic.substitution subst body
    )
  possible_arg_vars
      

  
