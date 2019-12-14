module Seq = Base.Sequence

module type SYNTHESIZER = sig
  
  val  f: Hfl.Equations.t -> PathEnv.t -> Id.t -> Hfl.sort -> spec:Hfl.fhorn -> Program.t
     
end


                      
(* 試しに第1級モジュールでパラメータを扱ってみる *)
let generator data_env qualifiers ~e_max:e_max_size ~scrutinee_max_size=
  (module struct
     module GenEtermsScrutinee = (val (GenEterms.generator ~size_max:scrutinee_max_size))     
     module GenEterms = (val (GenEterms.generator ~size_max:e_max_size))
                      
     type matchConditionInfo = {dataName:Id.t;
                                scrutinee: Id.t;
                                sclarConstructor: Id.t;
                               }
                             
     let inspect_condition_is_equal_to_match cond_list =
       
       let open BaseLogic in
       match cond_list with
       |[cond] ->
         begin
           match cond with
           |Eq ((Var (bsort, x)),
                  Cons (bsort', scalar_cons, []))
            
            |Eq ((Cons (bsort', scalar_cons, [])),
                   Var (bsort, x))
            ->
             (assert (bsort = bsort'));
             let sort = Hfl.of_baseLogic_sort bsort in
             (match sort with
              | `DataS i -> Some {dataName = i;
                                  scrutinee = x;
                                  sclarConstructor = scalar_cons
                                 }
              |_ -> assert false)
           |_ ->
             None
         end
       | _ -> None

            
     let add_penv_case_specific_info
           penv z scrutinee_prop (`Data data) DataType.{name = cons; args = arg_list}
       =
       let new_args = List.map (fun (x, sort) -> (Id.genid_from_id x, sort) ) arg_list in
       let penv =
         List.fold_right
           (fun (x, sort) penv' ->  PathEnv.add_bind x sort penv')
           (new_args :> (Id.t * Hfl.sort) list)
           penv
       in  
       let DataType.{constructor = cons'; args=args'; body = measure_constraint} = 
         DataType.Env.measure_constraint_of_constructor data_env (`DataS data) cons 
       in
       assert (cons' = cons);
       let equality_constraint = (* z = Cons x xs *)
         let open BaseLogic in
         Eq (Var (DataS(data,[]), z),
             Cons (DataS(data,[]), cons, List.map
                                       (fun (x,sort) -> Var (Hfl.to_baseLogic_sort sort, x))
                                       new_args)
            )
       in
       let measure_constraint = (* len z = len xs + 1 *)
         measure_constraint
         |> BaseLogic.replace Id.valueVar_id z
         |> List.fold_right2
              (fun (arg,_) (new_arg,_) e-> BaseLogic.replace arg new_arg e)
              args'
              new_args
       in
       let penv = penv
                  |> PathEnv.add_condition (`Base measure_constraint) 
                  |> PathEnv.add_condition (`Base equality_constraint) 
       in
       match scrutinee_prop with
       |None -> (penv, new_args)
       |Some (`Exists (bind, scrutinee_prop)) ->
         let arg_constraint =
           DataType.Env.unfold_clauses_diff
             data_env
             z DataType.{name=cons; args = new_args}
             scrutinee_prop
         in
         let penv = PathEnv.add_condition_list
                      arg_constraint
                      penv
         in
         (penv, new_args)

         


     let gen_e_term ep penv abduction_candidate sort spec =
       GenEterms.f ep penv abduction_candidate sort spec
       |> Seq.hd



     let get_sclar_constructor_spec ep sclar_con =
       match Hfl.Equations.find ep sclar_con with
       |Some (None, {params = _; args = []; body = `Horn ([], c)}) ->
         c
       |_ -> invalid_arg "get_sclar_constructor_spec"

         
                                
       
     let rec gen_b_term: Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.sort -> spec:Hfl.qhorn list 
                     -> Program.b option
       =
       (fun ep penv abduction_candidate sort ~spec ->
         match gen_branch_by_abduction ep penv abduction_candidate sort ~spec with
         |Some b -> Some b
         |None ->
           (* enumeration of match or use othere template  *)           
           invalid_arg "gen_b_term: not impl yet:(match enumeration)"
       )

     and gen_branch_by_abduction = 
       (fun ep penv abduction_candidate sort ~spec ->
         match gen_e_term ep penv abduction_candidate sort spec with
         |Some (e, _, abduction_candidate) ->
           let conds = AbductionCandidate.get abduction_candidate in
           if conds = [] then Some (Program.PE e)
           else
             begin
               match inspect_condition_is_equal_to_match conds with
               |Some {dataName = i; scrutinee = x; sclarConstructor = scon} ->
                 let scon_case =
                   Program.{constructor = scon;
                            argNames = [];
                            body = Program.PE e}
                 in
                 let other_cons = DataType.Env.list_constructor data_env i
                                  |> List.filter (fun (cons:DataType.constructor) -> cons.name <> scon)
                 in
                 (match gen_match_cases ep penv abduction_candidate
                                       ~scrutineeInfo:(x, None, i, other_cons)
                                       sort ~spec                 
                 with
                 |None -> None
                 |Some other_cases -> 
                 let open Program in
                 Some (PMatch (x, (Term (App {head = x; args = []})),
                               scon_case::other_cases)
                      ))
                 |None ->
                 let else_cond = BaseLogic.Not (BaseLogic.and_list conds) in
                 let penv' = PathEnv.add_condition (`Base else_cond) penv in
                 let abduction_candidate =
                   AbductionCandidate.initialize data_env penv' qualifiers ~new_vars:[] abduction_candidate
                 in
                 match gen_b_term ep penv' abduction_candidate sort ~spec with
                 |None -> None
                 |Some b_else -> 
                 let open Program in
                 Some (PIf ((Term (Formula (BaseLogic.and_list conds))),
                            (PE e),
                            b_else))
             end
         |None -> None)


     and gen_match_cases ep penv abduction_candidate
                         ~scrutineeInfo:(z, scrutinee_prop, data, cons_list)
                         sort ~spec
       =

       let penv' =
         match scrutinee_prop with
         |None -> penv
         |Some (`Exists (bind, cs)) -> PathEnv.add_condition_list cs penv
       in
       let penv_args_list =
         List.map
           (add_penv_case_specific_info penv' z scrutinee_prop (`Data data))
           cons_list
       in
         List.fold_left2
           (fun acc_case_opt DataType.{name = cons; args = _} (penv, new_arg) ->
             match acc_case_opt with
             |None -> None
             |Some acc_case -> 
               let abduction_candidate =
                 AbductionCandidate.initialize
                   data_env penv qualifiers ~new_vars:(List.map fst new_arg) abduction_candidate
               in
               match gen_b_term ep penv abduction_candidate sort ~spec with
               |None -> None
               |Some body -> 
                 Some (acc_case@[Program.{constructor = cons;
                                           argNames =new_arg;
                                           body = body }]))
           (Some [])
           cons_list
           penv_args_list


     (* and gen_match_by_scrutinee_enumeration ep penv abduction_candidate sort ~spec = *)
     (*   let scrutinee_e =  *)
       
     let inductive_arg (x, sort) clause =
       let open BaseLogic in
       match sort with
       | `IntS ->
          (match clause with
           | `Base (Le (Int lower, (Var (_,x')))) | `Base (Lt (Int lower, (Var (_,x'))))
             | `Base (Ge ((Var (_,x')), Int lower)) | `Base (Gt ((Var (_,x')), Int lower))
           when x = x'
             ->
              let new_x = Id.genid_from_id x in
              let clause' = `And (`Base (Lt (Var(IntS, new_x), Var(IntS, x))),
                                  Hfl.replace x new_x clause)
              in
              Some (new_x, clause')
           |_ -> None)

       | `DataS data ->
          (match DataType.Env.termination_measure data_env (`DataS data) with
           |[] ->
             None
          |measure::_ ->
            let tm = measure.name in
            let sort = DataS (data,[]) in
            let new_x = Id.genid_from_id x in
            let clause' = `And ((`Base (Lt (UF(IntS, tm, [Var(sort,new_x)]),
                                           UF(IntS, tm, [Var(sort, x)])))
                                ),
                                Hfl.replace x new_x clause)
                                
            in
            Some (new_x, clause'))
       | _ -> None

            
     let fresh_by_fresh_tbl fresh_tbl clause' =
       List.fold_left 
         (fun acc (x,x') -> Hfl.replace x x' acc)
         clause'                    
         fresh_tbl
       
     let rec mk_rec_spec_qhorn  args qhorn =
       match qhorn with
       | `Horn (pre_cs, c) ->
          assert (List.length pre_cs = List.length args);
          let inductive_arg_exist, args_cs', fresh_tbl =
            List.fold_left2
              (fun (inductive_arg_exist,acc, fresh_tbl) (x,sort) clause ->
                match inductive_arg (x,sort) clause with
                |Some (x', clause')when (not inductive_arg_exist) ->
                  (* fresh tblで更新 *)
                  let clause' = fresh_by_fresh_tbl fresh_tbl clause'
                  in
                  let fresh_tbl = (x,x')::fresh_tbl in
                  (true, acc@[(x', clause')], fresh_tbl)
                |_ ->
                  let new_x = Id.genid_from_id x in
                  let fresh_tbl = (x, new_x)::fresh_tbl in
                  let clause' = fresh_by_fresh_tbl fresh_tbl clause in
                  (inductive_arg_exist, acc@[(new_x, clause')], fresh_tbl))
            (false, [],[])            
            args
            pre_cs
          in
          let c' = fresh_by_fresh_tbl fresh_tbl c in
          let pre_cs' = List.map snd args_cs' in
          let args' = List.map2
                        (fun (new_x, _) (_, sort) -> (new_x, sort))
                        args_cs'
                    args
          in
          `Horn (pre_cs', c'), args'

       | `Exists (x, sort, qhorn) ->
          let qhorn', args' = mk_rec_spec_qhorn args qhorn in
          `Exists (x, sort, qhorn'), args'

       | `Forall (x, sort, qhorn) ->
          let qhorn', args' = mk_rec_spec_qhorn args qhorn in
          `Forall (x, sort, qhorn'), args'          

     let mk_rec_spec Hfl.{params = params; args = args; body = qhorn} =
       let qhorn', args' = mk_rec_spec_qhorn args qhorn in
       let params' =
         List.map (fun (p,sort) -> (Id.genid_from_id p, sort)) params
       in
       let qhorn' =
         List.fold_left2
           (fun acc (p,_) (new_p,_) ->
             Hfl.replace_qhorn p new_p acc)
           qhorn'
           params
           params'
       in
       Hfl.{params = params'; args = args'; body = qhorn' }



           
     let log_setting logcha ep =
       Printf.fprintf logcha "hfl equtaions:\n%s" (Hfl.Equations.to_string ep)
       
     let f: Hfl.Equations.t -> PathEnv.t -> Id.t -> Hfl.sort -> spec:Hfl.fhorn -> Program.t = 
       (fun ep penv name sort ~spec ->
         let Hfl.{params = params; args = args; body = qhorn} = spec in
         let rec_spec = mk_rec_spec spec in (* 再起するときの仕様 *)
         let rec_name = Id.genid_const (Id.to_string_readable name) in
         let logcha = open_out "setting.log" in
         let () = Hfl.Equations.add ep rec_name None rec_spec in
         let () = log_setting logcha ep in
         let () = close_out logcha in
         let penv = PathEnv.add_bind rec_name sort penv in (* 再起用に追加 *)
         let penv = PathEnv.add_bind_list args penv in
         let abduction_candidate =
           AbductionCandidate.initialize
             data_env penv qualifiers
             ~new_vars:(List.map fst args)
           AbductionCandidate.empty
         in
         match qhorn with
         | `Horn(cs, c) ->
            let penv = PathEnv.add_condition_list cs penv in
            let sort = (Hfl.return_sort sort:> Hfl.sort) in
            (match  gen_b_term ep penv abduction_candidate sort ~spec:[`Horn ([], c)] with
            |None -> raise (Not_found)
            |Some b -> 
            Program.PRecFun (name, args, b))
         | _ -> assert false    (* not impl *)
       )
       


   end
          :SYNTHESIZER)
         
