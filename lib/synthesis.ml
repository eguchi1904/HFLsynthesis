module Seq = Base.Sequence

module type SYNTHESIZER = sig
  
  val  f: Hfl.Equations.t -> PathEnv.t -> Id.t -> Hfl.sort -> spec:Hfl.fhorn -> Program.t
     
end


module Context:sig

  type t

  val empty: t

  val add_b: Program.b -> t -> t

  val size: t -> int

  val to_string: t -> string


end = struct

  type t = Program.b

  let empty = Program.PHole

  let log_cha = AppElimination.Log.log_cha


  let to_string  = Program.to_string_b 0              

  let log_context ctx =
    let () = Printf.fprintf
               log_cha
               "\nsynthesis....\n%s"
               (to_string ctx)
    in
    let () = Format.eprintf
               "\nsynthesis....\n%s@."
               (to_string ctx)
    in
    ()
            

  let add_b b t =
    let ctx = Program.subst_to_next_hole b t in
    let () = log_context ctx in
    ctx
    
  let rec size b =
    let open Program in
    match b with
    |PIf (_, b1, b2) ->
      1+ (max (size b1) (size b2))
    |PMatch(_, _, cases) ->
      1 + (List.fold_left
             (fun acc case -> max acc (size case.body))
             1 cases)
    |PFail |PHole |PE _ -> 1
        
        
end


module Log = struct
  

              
  let log_cha = AppElimination.Log.log_cha

  let log_context ctx =
    Printf.fprintf
      log_cha
      "synthesis....\n%s"
      (Context.to_string ctx)
     

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
         let scrutinee_prop' = List.map (Hfl.replace Id.valueVar_id z) scrutinee_prop in
         let penv = PathEnv.add_condition_list scrutinee_prop' penv in
         (penv, new_args)

         


     let gen_e_term ep penv abduction_candidate sort spec =
       GenEterms.f ep penv abduction_candidate sort spec




     let get_sclar_constructor_spec ep sclar_con =
       match Hfl.Equations.find ep sclar_con with
       |Some (None, {params = _; args = []; body = `Horn ([], c)}) ->
         c
       |_ -> invalid_arg "get_sclar_constructor_spec"

         
                                
       
     let rec gen_b_term: Context.t ->  Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.sort -> spec:Hfl.qhorn list 
                         -> Program.b Seq.t
       =
       (fun ctx ep penv abduction_candidate sort ~spec ->
         if Context.size ctx > 4 then Seq.empty
         else
         let b_by_abduction_seq =
           gen_branch_by_abduction ctx ep penv abduction_candidate sort ~spec
         in
         let b_by_scrutinee_enumeration = 
            gen_match_by_scrutinee_enumeration
                      ctx ep penv abduction_candidate sort ~spec
         in
         Seq.append
           b_by_abduction_seq
           b_by_scrutinee_enumeration
       )
                (* invalid_arg "gen_b_term: not impl yet:(use template)" *)

     and gen_branch_by_abduction  = 
       (fun ctx ep penv abduction_candidate sort ~spec ->
         Seq.concat_map
           (gen_e_term ep penv abduction_candidate sort spec)
        ~f:(fun (e, _, abduction_candidate) -> (* conditionと一緒に探している *)
          let conds = AbductionCandidate.get abduction_candidate in
           if conds = [] then Seq.singleton (Program.PE e)
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
                 
                 (match gen_match_cases ctx ep penv abduction_candidate
                                        ~scrutineeInfo:(x, (Program.Term (App {head = x; args = []})),None, i, other_cons)
                                        sort ~spec                 
                  with
                  |None -> Seq.empty
                  |Some other_cases -> 
                    let open Program in
                    Seq.singleton (PMatch (x, (Term (App {head = x; args = []})),
                                  scon_case::other_cases)
                 ))
               |None ->
                 let ctx =
                   let open Program in
                   Context.add_b (PIf  ((Term (Formula (BaseLogic.and_list conds))),
                                        (PE e),
                                        PHole)) ctx
                 in
                 let else_cond = BaseLogic.Not (BaseLogic.and_list conds) in
                 let penv' = PathEnv.add_condition (`Base else_cond) penv in
                 let abduction_candidate =
                   AbductionCandidate.initialize data_env penv' qualifiers ~new_vars:[] abduction_candidate
                 in
                 let b_else_seq = gen_b_term ctx ep penv' abduction_candidate sort ~spec in
                 Seq.map
                   b_else_seq
               ~f:(fun b_else -> 
                 let open Program in
                 (PIf ((Term (Formula (BaseLogic.and_list conds))),
                       (PE e),
                       b_else)))
             end
        )
       )



       
     and gen_match_cases ctx ep penv abduction_candidate
                         ~scrutineeInfo:(z, scrutinee_e, scrutinee_prop, data, cons_list)
                         sort ~spec
       =
       let penv_args_list =
         List.map
           (add_penv_case_specific_info penv z scrutinee_prop (`Data data))
           cons_list
       in
       let hole_cases =
         List.map2
           (fun DataType.{name = cons;args = _} (_, new_arg) ->
             Program.{constructor = cons;
                      argNames = new_arg;
                      body = PHole })
           cons_list
           penv_args_list         
       in
       let ctx = Context.add_b
                   (PMatch (z, scrutinee_e, hole_cases)) ctx
       in
       let ctx_cases_opt = 
         List.fold_left2
           (fun acc_case_opt DataType.{name = cons; args = _} (penv, new_arg) ->
             match acc_case_opt with
             |None -> None
             |Some (ctx, acc_case) ->
               if not (PathEnv.is_sat (PathEnv.expand 3 ep penv)) then
                 let ctx = Context.add_b Program.PFail ctx in
                 Some (ctx,(acc_case@[Program.{constructor = cons;
                                               argNames = new_arg;
                                               body = Program.PFail}]))
               else
                 let new_vars = if not (PathEnv.mem z penv) then
                                  z::(List.map fst new_arg)
                                else (List.map fst new_arg)
                 in
                 let abduction_candidate =
                   AbductionCandidate.initialize
                     data_env penv qualifiers ~new_vars abduction_candidate
                 in
                 match gen_b_term ctx ep penv abduction_candidate sort ~spec
                     |> Seq.hd  (* ここで複数を列挙する意味なし *)
                 with
                 |None -> None
                 |Some body ->
                   let ctx = Context.add_b body ctx in
                   Some (ctx, (acc_case@[Program.{constructor = cons;
                                                  argNames = new_arg;
                                                  body = body }])))
           ( Some (ctx,[]))
           cons_list
           penv_args_list
       in
       match ctx_cases_opt with
       |None -> None
       |Some (_, cases) -> Some cases
                         

     and is_constructor e =
       match e with
       |Program.Term (App {head = head;_}) -> DataType.Env.is_constructor data_env head
       |Program.Term _ -> false
       |Let (_,_,_,e) -> is_constructor e
                       
     (* ここは重い、はず *)
     and gen_match_by_scrutinee_enumeration ctx ep penv abduction_candidate sort ~spec =
       let scrutinee_e_seq =
         DataType.Env.fold_datatype
           (fun data_name _ acc ->
             let top_spec =[] in
             let data_sort = `DataS data_name in
             let scrutinee_seq = 
               GenEtermsScrutinee.f ep penv abduction_candidate data_sort top_spec
               |> Seq.map ~f:(fun elm -> (data_name, elm))
             in
             scrutinee_seq::acc)
           data_env
           []
       in
       Seq.filter_map
         (Seq.round_robin scrutinee_e_seq)
         ~f:(fun (data_name, (scrutinee_e, e_prop, abduction_candidate)) ->
           let () = Printf.fprintf Log.log_cha "enumerate match %s:\n"
                                   (Program.to_string_e scrutinee_e)
           in           
           if Program.size_e scrutinee_e <= 1 then None
           else if is_constructor scrutinee_e then None
           else
             let l = Id.genid "a" in
             let () = Printf.fprintf Log.log_cha "enumerate match %s:\n"
                                     (Program.to_string_e scrutinee_e)
             in
             let penv = PathEnv.add_bind l (`DataS data_name) penv in
             let cons_list = DataType.Env.list_constructor data_env data_name in
             match gen_match_cases ctx ep penv abduction_candidate
                                   ~scrutineeInfo:(l,scrutinee_e, Some e_prop, data_name, cons_list)
                                   sort ~spec
             with
             |None -> None
             |Some cases ->
               let open Program in
               Some (PMatch (l, scrutinee_e, cases)))

           
       
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
            let ctx = Context.empty in
            (match  gen_b_term ctx ep penv abduction_candidate sort ~spec:[`Horn ([], c)]
                    |> Seq.hd
             with
            |None -> raise (Not_found)
            |Some b -> 
            Program.PRecFun (name, args, b))
         | _ -> assert false    (* not impl *)
       )
       


   end
          :SYNTHESIZER)
         
