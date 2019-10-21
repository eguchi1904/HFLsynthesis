module Seq = Base.Sequence

module type SYNTHESIS = sig
  val gen_b_term:Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.sort -> spec:Hfl.qhorn list 
                 -> Program.b
end


                      

                      
(* 試しに第1級モジュールでパラメータを扱ってみる *)
let generator data_env qualifyer e_depth =
  (module struct

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
         DataType.Env.measure_constructor_of_constructor data_env (`Data data) cons 
       in
       assert (cons' = cons);
       match scrutinee_prop with
       |None -> penv
       |Some (`Exists (bind, scrutinee_prop)) ->
         let arg_constraint =
           DataType.Env.unfold_clauses_diff
             data_env
             z DataType.{name=cons; args = new_args}
             scrutinee_prop
         in
         let penv = PathEnv.add_condition_list
                      ((`Base measure_constraint)::arg_constraint)
                      penv
         in
         penv

     let mk_match_case_penv_list z scrutinee_prop (`Data data) penv =
       let cons_list = DataType.Env.list_constructor data_env data in (*  *)
       let penv' =
         match scrutinee_prop with
         |None -> penv
         |Some (`Exists (bind, cs)) -> PathEnv.add_condition_list cs penv
       in
       List.map (add_penv_case_specific_info penv' z scrutinee_prop (`Data data)) cons_list

     let gen_e_term ep penv abduction_candidate sort spec =
       GenEterms.f ep penv abduction_candidate sort spec e_depth
       |> Seq.hd

     type matchConditionInfo = {dataName:Id.t;
                                scrutinee: Id.t;
                                sclarConstructor: Id.t;
                               }

     let get_sclar_constructor_spec ep sclar_con =
       match Hfl.Equations.find ep sclar_con with
       |Some (None, {params = _; args = []; body = `Horn ([], c)}) ->
         c
       |_ -> invalid_arg "get_sclar_constructor_spec"
         
                                
       
     let rec gen_b_term: Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.sort -> spec:Hfl.qhorn list 
                     -> Program.b
       =
       (fun ep penv abduction_candidate sort ~spec ->
         match gen_branch_by_abduction ep penv abduction_candidate sort ~spec with
         |Some b -> b
         |None -> assert false  (* enumeration of match or use othere template  *)
                
       )

     and gen_branch_by_abduction = 
       (fun ep penv abduction_candidate sort ~spec ->
         match gen_e_term ep penv abduction_candidate sort spec with
         |Some (e, e_prop, abduction_candidate) ->
           let conds = AbductionCandidate.get abduction_candidate in
           if conds = [] then Some (Program.PE e)
           else
             begin
               match inspect_condition_is_equal_to_match conds with
               |Some {dataName = i; scrutinee = x; sclarConstructor = scon} ->
                 assert false
               |None ->
                 let else_cond = BaseLogic.Not (BaseLogic.and_list conds) in
                 let penv' = PathEnv.add_condition (`Base else_cond) penv in
                 let abduction_candidate = AbductionCandidate.initialize penv' abduction_candidate in
                 let b_else =  gen_b_term ep penv' abduction_candidate sort ~spec in
                 let open Program in
                 Some (PIf ((PredCond (BaseLogic.and_list conds)),
                            (PE e),
                            b_else))
             end
         |None -> None)


     and inspect_condition_is_equal_to_match cond_list =
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
         end
       | _ -> None
   end
          :SYNTHESIS)
         
