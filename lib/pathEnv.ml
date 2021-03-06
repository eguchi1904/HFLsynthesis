module List = Base.List

type t = {
    eqEnv:SolveEquality.Env.t;
    condition:Hfl.clause list;
    yetExpandApps: [`App of Hfl.application] list; (* sub set of conction *)
    sortEnv:MlEnv.t
         }         

let empty = {eqEnv = SolveEquality.Env.empty
            ;yetExpandApps = []
            ;condition = []
            ;sortEnv = MlEnv.empty}

let mem x t=
  MlEnv.mem x t.sortEnv
  

let to_string t =
  let yet_expand_str =
    List.map ~f:(Hfl.clause_to_string) (t.yetExpandApps:> Hfl.clause list)
    |> String.concat "; "
  in
  let cond_str =
    List.map ~f:(Hfl.clause_to_string) t.condition
    |> String.concat "; "
  in
  let eq_env_str =SolveEquality.Env.to_string t.eqEnv in
  "bindings:"
  ^"\n"^(MlEnv.to_string t.sortEnv)
  ^"\npath conditions:"
  ^"\n"^"(("^yet_expand_str^"))"^cond_str
  ^"\neq_env_str:\n"^eq_env_str
    
    
let extract_measure_info data_env c=
  let open BaseLogic in
  match c with
    | `Base (Eq (Var (DataS (data,[]), l),
                 Cons (_, cons, real_args)))
      | `Base (Eq (Cons (_, cons, real_args),Var (DataS (data,[]), l)))
      -> 
    let DataType.{constructor = _; args=args'; body = measure_constraint} = 
      DataType.Env.measure_constraint_of_constructor data_env (`DataS data) cons 
    in
    let args_to_real_args_sita =
      M.add_list2 (List.map ~f:fst args') real_args M.empty
    in
    let measure_constraint = (* len z = len xs + 1 *)
      measure_constraint
      |> BaseLogic.replace Id.valueVar_id l
      |>  BaseLogic.substitution args_to_real_args_sita
    in
    Some measure_constraint
    | _ -> None


let rec add_measure_info data_env c =
let open BaseLogic in
  match c with
    | `Base (Eq (Var (DataS (data,[]), l),
                 Cons (_, cons, real_args)))
      | `Base (Eq (Cons (_, cons, real_args),Var (DataS (data,[]), l)))
      -> 
    let DataType.{constructor = _; args=args'; body = measure_constraint} = 
      DataType.Env.measure_constraint_of_constructor data_env (`DataS data) cons 
    in
    let args_to_real_args_sita =
      M.add_list2 (List.map ~f:fst args') real_args M.empty
    in
    let measure_constraint = (* len z = len xs + 1 *)
      measure_constraint
      |> BaseLogic.replace Id.valueVar_id l
      |>  BaseLogic.substitution args_to_real_args_sita
    in
    `And (c, `Base measure_constraint)
    |`Base _ -> c
    |`And (c1, c2) ->
       `And (add_measure_info data_env c1, add_measure_info data_env c2)
    |`Or (c1, c2) ->
       `Or (add_measure_info data_env c1, add_measure_info data_env c2)
    |_ -> c



let update_eq_env_be_baselogic_term base_e eq_env =
  let open BaseLogic in
  match base_e with
  |Eq (e1, e2) ->
     SolveEquality.Env.add e1 e2 eq_env
  |Le (Var (IntS, n), upper)
   | Ge (upper, Var (IntS, n)) ->
     SolveEquality.Env.add_upper_bound n upper eq_env
  |Lt (Var (IntS, n), upper)
   |Gt (upper, Var (IntS, n))
    ->
     let upper = Minus (upper, Int 1) in
     SolveEquality.Env.add_upper_bound n upper eq_env
  |Le (lower, Var (IntS, n))
   |Ge (Var (IntS, n), lower) ->
     SolveEquality.Env.add_lower_bound lower n eq_env
  |Lt (lower, Var (IntS, n))
   |Gt (Var (IntS, n), lower) ->
     let lower = Plus (lower, Int 1) in
     SolveEquality.Env.add_lower_bound lower n eq_env
  | _ ->
     eq_env

    
let add_condition_eq_env (c:Hfl.clause) env =
  let es =
    (Hfl.separate_by_and c)
    |> List.filter_map
         ~f:(function | `Base e -> Some e | _ -> None)
  in
  List.fold_left
    es
    ~init:env
    ~f:(fun acc e -> update_eq_env_be_baselogic_term e acc)
  
  
  
    
let add_condition c env =
  match c with
  |`App _ as app_term -> 
  {yetExpandApps = app_term::env.yetExpandApps;
   eqEnv = env.eqEnv;
   condition = app_term::env.condition
   ;sortEnv  =env.sortEnv}

  | _ ->
     let c =add_measure_info (!DataType.Env.global_ref) c in
     let open BaseLogic in
    {yetExpandApps = env.yetExpandApps;
     condition = c::env.condition
     ;sortEnv  =env.sortEnv;
     eqEnv = add_condition_eq_env c env.eqEnv
    }     
 

let add_condition_list cs env =
  List.fold_left
    cs
    ~init:env
    ~f:(fun acc c ->
      add_condition c acc)

  
let add_bind i sort env =
  {yetExpandApps = env.yetExpandApps;
   eqEnv = env.eqEnv;
   condition = env.condition
  ;sortEnv = MlEnv.add i sort env.sortEnv
  }

let add_bind_list binds env =
  List.fold_right
    ~f:(fun (i, sort) acc -> add_bind i sort acc)
    binds
    ~init:env  
  
                   
let find_heads base env :HeadCandidates.t=
  MlEnv.find_heads base env.sortEnv

let extract_condition env = env.condition

open SolveEquality


let rec cut_unsat_path_from_or condition (`Or (c1, c2)) =
  let c1_list_opt = cut_unsat_path condition c1 in
  let c2_list_opt = cut_unsat_path condition c2 in
  match c1_list_opt, c2_list_opt with
  |None,_ -> c2_list_opt
  |_,None -> c1_list_opt
  |Some c1_list, Some c2_list ->
    Some [`Or (Hfl.concat_by_and c1_list, Hfl.concat_by_and c2_list)]

and cut_unsat_path conditions c =
  let cs = Hfl.separate_by_and c in
  let or_clauses, other_clauses =
    List.partition_map
      cs
      ~f:(function | (`Or _ as c) ->`Fst c | (_ as c) -> `Snd c)
  in
  let check_clauses =
    empty
    |> add_condition_list conditions
    |> add_condition_list other_clauses
    |> extract_condition
  in
  let check_clauses_z3 =
    check_clauses
    |> List.map ~f:UseZ3.clause_to_z3_expr
    |> List.map ~f:fst
  in
  let is_sat = UseZ3.bind_and_list check_clauses_z3
               |> UseZ3.is_satisfiable
  in
  if not is_sat then None
  else
    let or_clauses_resutls =
      List.map
        ~f:(fun or_clause -> cut_unsat_path_from_or conditions or_clause )
        or_clauses
    in
    let or_sat_clauses, nones =
      List.partition_map
        or_clauses_resutls
        ~f:(function Some cs -> `Fst cs |None -> `Snd None)
    in
    if nones <> [] then
      None
    else
      Some (other_clauses@(List.concat or_sat_clauses))



(* 今はとりあえず、単純に全ての等号をとってくる *)
let separate_eq_cons_for_exists_instantiation ~exists:exists' cs =
  (ignore exists');
  List.partition_map
    cs
    ~f:(function
        | `Base (BaseLogic.Eq (e1, e2)) -> `Fst (e1, e2)
        |  c -> `Snd c)
      
  
let try_expand ep eq_env conditions (`App  Hfl.{head = head; args = arg_cs;_}) =
  (* let () = Format.eprintf "try expand:%s@." (Id.to_string_readable head) in *)
  match Hfl.Equations.find ep head with
  |None -> assert false       
  |Some (_, {params = params; args = args; body = qhorn}) ->
    (assert (params = []));
    (assert (List.length args = List.length arg_cs));
    (* 引数の代入 *)
    let qhorn = Hfl.subst_qhorn
                  (M.add_list2 (List.map ~f:fst args) arg_cs M.empty)
                  qhorn
    in
    (* toplevelのexists束縛を分離 *)
    let exists, qhorn = Hfl.split_outside_exists qhorn in
    let exists' = List.map ~f:(fun (id,sort) ->Id.genid_from_id id, sort) exists in
    let exists' = (exists' :> (Id.t * Hfl.sort) list) in
    let qhorn = List.fold2_exn
                  exists
                  exists'
                  ~init:qhorn
                  ~f:(fun acc (id,_) (id',_) -> Hfl.replace_qhorn id id' acc)
    in
    let `Horn (cs, c) = match qhorn with | `Horn _ as horn -> horn | _ -> assert false in
    (* exist束縛変数のfresh *)        
    (assert (cs = []));            (* not impl *)
    match cut_unsat_path conditions c with
    |None -> Some [`Base (BaseLogic.Bool false) ] (* unsatであることが発覚 *)
    |Some body_cs ->
      let body_cs_str = 
          List.map ~f:(Hfl.clause_to_string) body_cs
          |> String.concat "; "
      in
      (* let () = Format.eprintf "body is...:\n%s@." body_cs_str in *)
    if
      List.for_all              (* existsがbody_csに出てこない *)
        ~f:(fun c ->
          List.for_all
            ~f:(fun (x, _) -> not (S.mem x (Hfl.fv c)))
            exists')
        body_cs
    then Some body_cs
    else
      let eq_cons, body_other_cs = separate_eq_cons_for_exists_instantiation
                                   ~exists:exists' body_cs
      in
      let exists_for_eq = List.map ~f:fst exists' in
      match Base.Sequence.hd (SolveEquality.f ~exists:exists_for_eq eq_env eq_cons) with
      |None -> None       
      |Some sita ->
        let sita_str =
          M.fold
            (fun i e acc ->
              (Id.to_string_readable i)^"-->"
              ^(BaseLogic.p2string e)
              ^"; "
              ^acc)
            sita
            ""
        in 
        (* let () = Format.eprintf "  sita:%s@." sita_str in *)
        let remain_exists = List.filter  ~f:(fun x -> not (M.mem x sita)) exists_for_eq in
        if remain_exists = [] then
          let body_other_cs = List.map ~f:(Hfl.subst_base_term sita ) body_other_cs in
          Some body_other_cs
        else                    (* exists が全て決まらなかった場合 *)
          let body_other_cs = List.map ~f:(Hfl.subst_base_term sita ) body_other_cs in
          Some body_other_cs          

          (* let body_other_cs =
           *   body_other_cs
           *   (\* 未解決のexistが含まれれるclauseをfilterする *\)
           *   |> List.filter
           *        ~f:(fun c ->
           *          not (List.exists ~f:(fun x -> S.mem x (Hfl.fv c)) remain_exists))
           *   |> List.map ~f:(Hfl.subst_base_term sita )
           * in
           * if body_other_cs = [] then
           *   (\* let () = Format.eprintf "\nnone~~~\n@." in *\)
           *   None
           * else
           *   let body_other_cs_str = 
           *     List.map ~f:(Hfl.clause_to_string) body_other_cs
           *     |> String.concat "; "
           *   in
           *   (\* let () = Format.eprintf "\nreturn:%s@." body_other_cs_str in *\)
           *   Some body_other_cs *)


             
let expand' ep t =
  let remain_yet_expand, expanded_cs = 
    List.fold_left
      t.yetExpandApps
      ~init:([], [])
      ~f:(fun (remain_yet_expand, expanded_cs) app_term ->
        match try_expand ep t.eqEnv t.condition app_term with
        |Some new_expand_cs ->
          (remain_yet_expand, new_expand_cs@expanded_cs)
        |None ->
          (app_term::remain_yet_expand, expanded_cs))
  in
  {eqEnv = t.eqEnv;
   condition = t.condition;
   yetExpandApps = remain_yet_expand;
   sortEnv = t.sortEnv}
  |> add_condition_list expanded_cs
    
  
let rec expand i ep t =
  if i <= 0 then t
  else
    expand (i-1) ep (expand' ep t)

let is_sat t =
  t.condition 
  |> List.map ~f:UseZ3.clause_to_z3_expr
  |> List.map ~f:fst
  |> UseZ3.bind_and_list
  |> UseZ3.is_satisfiable  


          
