module Seq = Base.Sequence

module type SYNTHESIZER = sig
  
  val  f: Hfl.Equations.t -> PathEnv.t -> Id.t -> Hfl.sort -> spec:Hfl.fhorn -> Program.t
     
end


                      
(* 試しに第1級モジュールでパラメータを扱ってみる *)
let generator data_env qualifiers e_depth =
  (module struct

     type matchConditionInfo = {dataName:Id.t;
                                scrutinee: Id.t;
                                sclarConstructor: Id.t;
                               }
                             
     let  inspect_condition_is_equal_to_match cond_list =
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
           |_ -> None
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

         


     let gen_e_term ep penv abduction_candidate sort spec =
       GenEterms.f ep penv abduction_candidate sort spec e_depth
       |> Seq.hd



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
         |None ->
           (* enumeration of match or use othere template  *)           
           invalid_arg "gen_b_term: not impl yet"
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
                 let other_cases =
                   gen_match_cases ep penv abduction_candidate
                                   ~scrutineeInfo:(x, None, i, other_cons)
                   sort ~spec
                 in
                 let open Program in
                 Some (PMatch ({head = x; args = []},
                               scon_case::other_cases)
                      )
               |None ->
                 let else_cond = BaseLogic.Not (BaseLogic.and_list conds) in
                 let penv' = PathEnv.add_condition (`Base else_cond) penv in
                 let abduction_candidate =
                   AbductionCandidate.initialize penv' qualifiers ~new_vars:[] abduction_candidate
                 in
                 let b_else =  gen_b_term ep penv' abduction_candidate sort ~spec in
                 let open Program in
                 Some (PIf ((PredCond (BaseLogic.and_list conds)),
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
       let penv_list =
         List.map
           (add_penv_case_specific_info penv' z scrutinee_prop (`Data data))
           cons_list
       in
       List.map2
         (fun DataType.{name = cons; args = arg_list} penv ->
           let abduction_candidate =
             AbductionCandidate.initialize
               penv qualifiers ~new_vars:(List.map fst arg_list) abduction_candidate
           in
           Program.{constructor = cons;
                    argNames = arg_list;
                    body = gen_b_term ep penv abduction_candidate sort ~spec})
         cons_list
         penv_list


     let mk_rec_spec penv spec = spec (* ひとまず、いや一瞬で必要にあるな。全ての入力にlet f x　= f xが帰るので*)
       
     let f: Hfl.Equations.t -> PathEnv.t -> Id.t -> Hfl.sort -> spec:Hfl.fhorn -> Program.t = 
       (fun ep penv name sort ~spec ->
         let Hfl.{params = params; args = args; body = qhorn} = spec in
         let rec_spec = mk_rec_spec penv spec in
         let () = Hfl.Equations.add ep name None rec_spec in
         let penv = PathEnv.add_bind_list args  penv in
         let abduction_candidate =
           AbductionCandidate.initialize
             penv qualifiers
             ~new_vars:(List.map fst args)
           AbductionCandidate.empty
         in
         match qhorn with
         | `Horn(cs, c) ->
            let penv = PathEnv.add_condition_list cs penv in
            let b = gen_b_term ep penv abduction_candidate sort ~spec:[`Horn ([], c)] in
            Program.PRecFun (name, args, b)
         | _ -> assert false    (* not impl *)
       )
       


   end
          :SYNTHESIZER)
         
