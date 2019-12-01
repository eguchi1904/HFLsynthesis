module List = Base.List
open List.Or_unequal_lengths

let expansion_max = 1

let subst_base_term_horn sita =
  fun (`Horn (cs, c)) ->
          `Horn (List.map ~f:(Hfl.subst_base_term sita) cs,
                 Hfl.subst_base_term sita c)

module Premise:sig
  type t

  val empty:t

  val show: t -> Hfl.clause list

  val add:Hfl.clause -> t -> t

  val show_equality_env: t -> SolveEquality.Env.t



end = struct

  type t = {generalPremise:Hfl.clause list;
            equalityPremise:SolveEquality.Env.t
           }


  let empty = {generalPremise = [];
               equalityPremise = SolveEquality.Env.empty}
            
  let show t = t.generalPremise

  let add c t = 
    {generalPremise = c::t.generalPremise;
     equalityPremise = match c with
                       | `Base BaseLogic.Eq (e1, e2) ->
                          SolveEquality.Env.add e1 e2 t.equalityPremise
                       | _ ->
                          t.equalityPremise
    }
 
  let show_equality_env t = t.equalityPremise
                         
end

let rec separate_toplevel_apps (clause:Hfl.clause) =
  match clause with
  | `App application -> ([application], [])
  | `And (c1,c2) ->
     let apps1, c1' = separate_toplevel_apps c1 in
     let apps2, c2' = separate_toplevel_apps c2 in
     (apps1@apps2, c1'@c2')
  | e -> ([], [e])

       

let decompose_abst_terms_implication (`Abs (args1, body1)) (`Abs (args2, body2)) =
  match
    List.fold2
      ~init:body2
      ~f:(fun body (x,_) (x',_) -> Hfl.replace x' x body)
      args1
      args2
  with
  |Unequal_lengths -> assert false
  |Ok body2 ->
    (body1, body2)

  
(* うーん *)
let decompose_application_terms_implication_by_monotonicity:
      Hfl.topSort -> Hfl.application -> Hfl.application
      -> (BaseLogic.t * BaseLogic.t * BaseLogic.sort) list 
         * ((Hfl.clause * Hfl.clause) list )=
  (fun head_sort
       {head = head; params = params1; args = args1}
       {head = head'; params = params2; args = args2} ->
    if head <> head' then invalid_arg " docompose "
    else
      ((assert (params1 = params2 && params2 = []));
        match head_sort with
        | `BoolS -> assert (args1 = []);
                    ([],[])
        | `FunS (arg_sorts, `BoolS) ->
           match List.map3 args1 args2 arg_sorts ~f:(fun c1 c2 sort -> (c1, c2, sort)) with
           |Unequal_lengths -> assert false
           |Ok arg_constraints ->
             let eq_cons, ineq_cons =
               List.partition_map
                 arg_constraints
                 ~f:(fun (c1,c2,sort) ->
                       match sort with
                       | `IntS | `DataS _ | `SetS _ as bsort ->
                          (match c1, c2 with
                          | `Base b1, `Base b2 -> 
                             `Fst (b1, b2, Hfl.to_baseLogic_sort bsort)
                          | _ -> assert false )
                       | `BoolS -> `Snd (c1, c2)
                       | `FunS _ ->
                          match c1, c2 with
                          | (`Abs _ as c1), (`Abs _ as c2) ->
                             `Snd (decompose_abst_terms_implication c1 c2)
                          | _ -> assert false
                 )
             in
             eq_cons, ineq_cons
      )
  )
  


let rec solve_inequality_constraints:
      int
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> BaseLogic.t M.t
      -> premise:Premise.t
      ->((Hfl.clause * Hfl.clause) list )
      -> (BaseLogic.t M.t * (Hfl.horn list)) option =
  (fun expand_count ~exists:binds ep sita ~premise ineq_cons ->
    List.fold_left
          ~init:(Some (sita, []))
          ~f:(fun acc (c1, c2) ->
            match acc with
            |None -> None
            |Some (sita, acc_list) -> 
              let c1 = Hfl.subst_base_term sita c1 in
              let c2 = Hfl.subst_base_term sita c2 in
              let premise = Premise.add c1 premise in
              (match eliminate_app expand_count ~exists:binds ep ~premise c2 with
               |None -> None                                  
               |Some (sita', horn_list) ->
                Some (
                    (M.union (fun _ -> assert false) sita sita'),
                    horn_list@acc_list
                  )
              )
          )
          ineq_cons
  )
(* solveするよりか、 eqだけといて制約たちを返す、という方がよっぽどの嬉しさがあるな。 *)
(* そうしよう *)
and solve_equality_inequality_constraints:
      int
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      ->  (BaseLogic.t * BaseLogic.t * BaseLogic.sort) list 
          * ((Hfl.clause * Hfl.clause) list )
      -> (BaseLogic.t M.t * (Hfl.horn list)) option =
  (fun expand_count ~exists:binds ep ~premise (eq_cons, ineq_cons) ->
    let equality_env = Premise.show_equality_env premise in
    (* 結局sortは必要なかったのでad-hocにここで削除 *)
    let eq_cons = List.map ~f:(fun (e1, e2, _) -> (e1, e2)) eq_cons in
    match SolveEquality.f ~exists:(List.map ~f:fst binds) equality_env eq_cons with
    |None -> None
    |Some sita ->
      (* in_eq_consをどうにかする *)
      let binds = List.filter binds ~f:(fun (id, _) -> not (M.mem id sita)) in
      (match solve_inequality_constraints
              expand_count  ~exists:binds ep sita ~premise ineq_cons
       with
       |None -> None
       |Some (sita, implications) ->
         (* sitaの代入 *)
         let implications =
           List.map
             implications
             ~f:(subst_base_term_horn sita)
         in
         Some (sita, implications)
      )
  )


(* 結論からapplicationのtermを消し去りたい。 *)
(* rDataはいらない、ということにしようとり会えず *)
(* これ本当は、Seqを返すとするのが良いんだろうな。まずは動かしたいのであれだけど *)
and solve_application:
      int 
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      -> Hfl.application
      -> (BaseLogic.t M.t * (Hfl.horn list)) option
  =
  (fun expand_count ~exists:binds ep ~premise ({head = head;_} as app) ->
    let head_sort = match Hfl.Equations.find_sort ep head with None -> assert false | Some sort -> sort in
    let app_terms_in_premise =
      List.filter_map
        (Premise.show premise)
        ~f:(function
            | `App (Hfl.{head = head';_}as app) when head = head' -> Some app
            | _ -> None)
    in
    let ineq_constraints =
      List.map
        app_terms_in_premise      
        ~f:(fun premise_app ->
          decompose_application_terms_implication_by_monotonicity head_sort premise_app app
        )
    in
    List.find_map
      ineq_constraints
      ~f:(solve_equality_inequality_constraints expand_count ~exists:binds ep ~premise)
  )

and solve_application_expand_if_fail:
      int 
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      -> Hfl.application
      -> (BaseLogic.t M.t * (Hfl.horn list)) option =
  (fun expand_count ~exists:binds ep ~premise ({head = head; args = arg_cs;_} as app) ->
    match solve_application expand_count ~exists:binds ep ~premise app with
    |Some result -> Some result
    |None -> 
      if expand_count >= expansion_max then None
      else
        (* 展開してみる *)
      match Hfl.Equations.find ep head with
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
        (* exist束縛変数のfresh *)        
        let exists' = List.map ~f:(fun (id,sort) ->Id.genid_from_id id, sort) exists in
        let qhorn = List.fold2_exn
                      exists
                      exists'
                      ~init:qhorn
                      ~f:(fun acc (id,_) (id',_) -> Hfl.replace_qhorn id id' acc)
        in
        (match qhorn with
          | `Horn (head_spec_pre, head_spec_result) ->
           let binds = (exists':>(Id.t * Hfl.sort) list)@binds in
           let premise = List.fold_right ~f:Premise.add ~init:premise head_spec_pre in
           (* expand_count がincrementされるのはここのみ *)
           eliminate_app (expand_count+1) ~exists:binds ep ~premise head_spec_result
          | _ -> invalid_arg "solve_application_expand:not yet impl")
      |None -> assert false
  )


and solve_application_list:
      int 
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      -> Hfl.application list
      -> BaseLogic.t M.t
      -> Hfl.horn list
      -> (BaseLogic.t M.t * (Hfl.horn list)) option
  =
  (fun expand_count ~exists:binds ep ~premise apps acc_sita acc_horn ->
    match apps with
    |[] ->
    let acc_horn =
      List.map
      acc_horn
      ~f:(subst_base_term_horn acc_sita)
    in                     
      Some (acc_sita, acc_horn)
    |{head = head; params= params; args = args}::other ->
      (* sitaの適用 *)
      let params = List.map ~f:(Hfl.subst_base_term_abs acc_sita) params in
      let args = List.map ~f:(Hfl.subst_base_term acc_sita) args in
      let app = Hfl.{head = head; params= params; args = args} in
      (match solve_application_expand_if_fail expand_count ~exists:binds ep ~premise app with
       |None -> None
       |Some (sita', horns) ->
         let acc_sita = M.union (fun _ -> assert false) acc_sita sita' in
         let acc_horn = horns@acc_horn in
         let binds = List.filter binds ~f:(fun (id, _) -> not (M.mem id acc_sita)) in
         solve_application_list
           expand_count ~exists:binds ep ~premise other acc_sita acc_horn
      )
  )

  
and eliminate_app_from_or_clause
     expand_count ~exists:binds ep ~premise (`Or (c1,c2))
    :(BaseLogic.t M.t * (Hfl.horn list)) option =
  if not (Hfl.app_term_exist (`Or (c1, c2))) then
    Some (M.empty, [`Horn ((Premise.show premise), (`Or (c1, c2)))])
  else
    let c_small, c_big =
      if Hfl.size c1 < Hfl.size c2 then c1, c2 else c2, c1
    in
    match eliminate_app expand_count ~exists:binds ep ~premise c_small with
    |None ->
      eliminate_app expand_count ~exists:binds ep ~premise c_big
    |Some (sita, horn_list) ->
      let c_small_valid =
        List.for_all
          horn_list
          ~f:(fun horn -> UseZ3.horn_to_z3_expr horn |> UseZ3.is_valid)
      in
      if c_small_valid then
        Some (sita, [])
      else
        eliminate_app expand_count ~exists:binds ep ~premise c_big


and eliminate_app_from_or_clause_list
      expand_count ~exists:binds ep ~premise or_clauses acc_sita acc_horn
    :(BaseLogic.t M.t * (Hfl.horn list)) option  =
  match or_clauses with
  |[] ->
    (* 最後に代入 *)
    let acc_horn =
      List.map
      acc_horn
      ~f:(subst_base_term_horn acc_sita)
    in                     
    Some (acc_sita, acc_horn)
  |or_clause::other ->
    (* acc_sitaの適用 *)
    let or_clause = Hfl.subst_base_term acc_sita or_clause
                    |> (function |`Or _ as or_term -> or_term | _ ->assert false)
    in
    (match eliminate_app_from_or_clause
             expand_count ~exists:binds ep ~premise or_clause
     with
     |None -> None
     |Some (sita', horns) ->
       let acc_sita = M.union (fun _ -> assert false) acc_sita sita' in
       let acc_horn = horns@acc_horn in
       let binds = List.filter binds ~f:(fun (id, _) -> not (M.mem id acc_sita)) in
       eliminate_app_from_or_clause_list
         expand_count ~exists:binds ep ~premise other acc_sita acc_horn
    )


and eliminate_app expand_count ~exists:binds ep ~premise clause =
  let toplevel_apps, other_clauses = separate_toplevel_apps clause in
  match solve_application_list
          expand_count ~exists:binds ep ~premise toplevel_apps M.empty []
  with
  |None -> None                 (* app-termがequality的に成立しない *)
  |Some (sita, horn_list_from_app) ->
    let binds = List.filter binds ~f:(fun (id, _) -> not (M.mem id sita)) in
    let or_clauses_with_app_term, other_clauses =
      List.partition_map
        other_clauses
        ~f:(function | (`Or _ as c) ->
                        if Hfl.app_term_exist c then
                          `Fst c  else `Snd c
                     | (_ as c) -> `Snd c)
    in
    (match eliminate_app_from_or_clause_list
             expand_count
             ~exists:binds ep ~premise or_clauses_with_app_term M.empty []
     with
     |None -> None
     |Some (sita', horns_from_or) ->
       let sita = M.union (fun _ -> assert false) sita sita' in
       (* sitaの適用 *)
       let other_clauses_horn =
         `Horn ((Premise.show premise), Hfl.concat_by_and other_clauses)
         |> subst_base_term_horn sita
       in
       let horn_list_from_app =
         List.map ~f:(subst_base_term_horn sita) horn_list_from_app
       in
       Some (sita, other_clauses_horn::(horn_list_from_app@horns_from_or)))



    
let f ~exists:binds ep penv clause =
  let premise = List.fold_right
                  ~f:Premise.add
                  (PathEnv.extract_condition penv)
                  ~init:Premise.empty
  in
  eliminate_app 0 ~exists:binds ep ~premise clause


  
  
