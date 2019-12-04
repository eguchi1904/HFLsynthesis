module List = Base.List
open List.Or_unequal_lengths
module Seq = Base.Sequence

type solution = BaseLogic.t M.t * (Id.t * Hfl.sort) list * (Hfl.horn list)
let expansion_max = 1

let subst_base_term_horn sita =
  fun (`Horn (cs, c)) ->
          `Horn (List.map ~f:(Hfl.subst_base_term sita) cs,
                 Hfl.subst_base_term sita c)


let is_exists_free_horn sita ~exists (`Horn (cs, c)) =
  let exists_vars =             (* sitaで割り当てらていない存在束縛された変数 *)
    List.map exists ~f:fst
    |> List.filter ~f:(fun x -> not (M.mem x sita))
  in
  List.for_all                  (* 全てのexists変数が、fv(c::cs)に出現しない *)
    exists_vars
    ~f:(fun x ->
      List.for_all
        (c::cs)
        ~f:(fun c -> not (S.mem x (Hfl.fv c)))
    )

let rec pre_check_horns sita ~exists horns =
  match horns with
  |[] -> Some []
  |horn::xs ->
    if is_exists_free_horn sita ~exists horn then
      let horn = subst_base_term_horn sita horn in
      if UseZ3.horn_to_z3_expr horn |> UseZ3.is_valid then
        pre_check_horns sita ~exists xs
      else
        None
    else
      (match pre_check_horns sita ~exists xs with
       |None -> None
       |Some horns -> Some (horn::horns))

        
(* 結果をandでまとめる *)
(* この時に、T/Fが判定できるhornは先に判定する。この判定は良い感じに遅延される *)
(* existsは新たな差分を返す *)
let rec bind_solutions
        :BaseLogic.t M.t
         -> exists:(Id.t * Hfl.sort) list
         -> 'a list
         -> f:(BaseLogic.t M.t -> 'a -> solution Seq.t)
         -> solution Seq.t =
  (fun sita ~exists l ~f ->
    match l with
    |[] -> Seq.singleton (sita, [], []) (* 量化子は差分を返すので *)
    |x::xs ->
      let solution_of_x = f sita x in
      Seq.concat_map
        solution_of_x
        ~f:(fun (sita, exists_x, horns_x) ->
          match pre_check_horns sita ~exists:(exists_x@exists) horns_x with
          |None -> Seq.empty
          |Some [] ->
            bind_solutions sita ~exists xs ~f
          |Some horns_x -> 
            bind_solutions sita ~exists xs ~f
            |> Seq.map
                 ~f:(fun (sita, exists_xs, horn_xs) ->(sita, exists_x@exists_xs, horns_x@horn_xs))
        )
  )
                      

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
      -> BaseLogic.t M.t
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      ->((Hfl.clause * Hfl.clause) list )
      -> solution Seq.t = 
  (fun expand_count sita ~exists:binds ep ~premise ineq_cons ->
    bind_solutions
      sita ~exists:binds ineq_cons
      ~f:(fun sita (c1, c2) ->
        let premise' = Premise.add c1 premise in
        eliminate_app expand_count sita ~exists:binds ep ~premise:premise' c2
        |> Seq.map
             ~f:(fun (sita, exists, horns) ->
               sita,
               exists, 
               List.map
                 horns
                 ~f:(fun (`Horn (pre, c))-> `Horn (c1::pre, c))
             )
  ))

(* solveするよりか、 eqだけといて制約たちを返す、という方がよっぽどの嬉しさがあるな。 *)
(* そうしよう *)
and solve_equality_inequality_constraints:
      int
      -> BaseLogic.t M.t  
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      ->  (BaseLogic.t * BaseLogic.t * BaseLogic.sort) list 
          * ((Hfl.clause * Hfl.clause) list )
      -> solution Seq.t = 
  (fun expand_count sita ~exists:binds ep ~premise (eq_cons, ineq_cons) ->
    let equality_env = Premise.show_equality_env premise in
    (* sitaの反映 *)
    let eq_cons =
      List.map
        eq_cons       
        ~f:(fun (e1, e2, _)
            -> (BaseLogic.substitution sita e1, BaseLogic.substitution sita e2))
    in
    let exists_for_solve_eq =
      List.map ~f:fst binds
      |> List.filter ~f:(fun id -> not (M.mem id sita))
    in
    match SolveEquality.f ~exists:exists_for_solve_eq equality_env eq_cons with (* ここには非決定性がないはずなので *)
    |None -> Seq.empty
    |Some sita' ->
      let sita = M.union (fun _ -> assert false) sita sita' in
      (* in_eq_consをどうにかする *)
       solve_inequality_constraints
              expand_count sita ~exists:binds ep ~premise ineq_cons
      )



(* 結論からapplicationのtermを消し去りたい。 *)
(* rDataはいらない、ということにしようとり会えず *)
(* これ本当は、Seqを返すとするのが良いんだろうな。まずは動かしたいのであれだけど *)
and solve_application:
      int
      -> BaseLogic.t M.t
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      -> Hfl.application
      -> solution Seq.t
  =
  (fun expand_count sita ~exists:binds ep ~premise ({head = head;_} as app) ->
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
    let solutions_for_ineq_constraints =
        (Seq.concat_map
           (Seq.of_list ineq_constraints)
           ~f:(solve_equality_inequality_constraints expand_count sita ~exists:binds ep ~premise))
    in
    if S.exists                 (* appにexists束縛変数があるなら *)
         (fun x -> List.mem (List.map ~f:fst binds) x ~equal:(=)
                   && not (M.mem x sita))
         (Hfl.fv (`App app))
    then
      Seq.append
        solutions_for_ineq_constraints
        (Seq.singleton (sita, [], [`Horn ([],(`App app))]))
    else
      solutions_for_ineq_constraints
  )
  

and solve_application_by_expand:
      int
      -> BaseLogic.t M.t  
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      -> Hfl.application
      -> solution Seq.t =
  (fun expand_count sita ~exists:binds ep ~premise {head = head; args = arg_cs;_} ->
    Seq.concat_map
      (Seq.singleton 1)         (* dummy:遅延させる為に *)
      ~f:(fun _ -> 
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
          (* exist束縛変数のfresh *)        
          let exists' = List.map ~f:(fun (id,sort) ->Id.genid_from_id id, sort) exists in
          let exists' = (exists' :> (Id.t * Hfl.sort) list) in
          let qhorn = List.fold2_exn
                        exists
                        exists'
                        ~init:qhorn
                        ~f:(fun acc (id,_) (id',_) -> Hfl.replace_qhorn id id' acc)
          in
          (match qhorn with
           | `Horn (head_spec_pre, head_spec_result) ->
              let binds = exists'@binds in
              let premise = List.fold_right ~f:Premise.add ~init:premise head_spec_pre in
              (* expand_count がincrementされるのはここのみ *)
              eliminate_app  (expand_count+1) sita ~exists:binds ep ~premise head_spec_result
              |> Seq.map        (* 展開で出てきた新規のexists'を追加する、existsが追加されるのはここのみ *)
                   ~f:(fun (sita, exists, horns) -> (sita, (exists'@exists), horns))
           | _ -> invalid_arg "solve_application_expand:not yet impl")
      )
  )
   
and solve_application_expand_if_fail:
      int
      -> BaseLogic.t M.t  
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      -> Hfl.application
      -> solution Seq.t =
  (fun expand_count sita ~exists:binds ep ~premise app ->
    let direct_solutions:solution Seq.t =
      solve_application expand_count sita ~exists:binds ep ~premise app in
   if expand_count >= expansion_max then
     direct_solutions
   else
     let expand_solutions =
       solve_application_by_expand expand_count sita ~exists:binds ep ~premise app
     in
     Seq.append direct_solutions expand_solutions
  )


and solve_application_list:
      int
      -> BaseLogic.t M.t
      -> exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> premise:Premise.t
      -> Hfl.application list
      -> solution Seq.t
  =
  (fun expand_count sita ~exists:binds ep ~premise apps ->
    bind_solutions
      sita apps ~exists:binds
      ~f:(fun sita app ->
        solve_application_expand_if_fail expand_count sita ~exists:binds ep ~premise app)
  )

  
and eliminate_app_from_or_clause
     expand_count sita ~exists:binds ep ~premise (`Or (c1,c2))
    :solution Seq.t =
  if not (Hfl.app_term_exist (`Or (c1, c2))) then
    Seq.singleton (M.empty, [], [`Horn ((Premise.show premise), (`Or (c1, c2)))])
  else
    let c_small, c_big =
      if Hfl.size c1 < Hfl.size c2 then c1, c2 else c2, c1
    in
    Seq.append
      (eliminate_app expand_count sita ~exists:binds ep ~premise c_small )
      (eliminate_app expand_count sita ~exists:binds ep ~premise c_big )    


and eliminate_app_from_or_clause_list
      expand_count sita ~exists:binds ep ~premise or_clauses 
    :solution Seq.t  =
  bind_solutions
    sita ~exists:binds
    or_clauses
    ~f:(fun sita or_clause ->
      eliminate_app_from_or_clause
             expand_count sita ~exists:binds ep ~premise or_clause)


and eliminate_app expand_count sita ~exists:binds ep ~premise clause =
  let toplevel_apps, other_clauses = separate_toplevel_apps clause in

  let or_clauses_with_app_term, other_clauses =
    List.partition_map
      other_clauses
      ~f:(function | (`Or _ as c) ->
                      if Hfl.app_term_exist c then
                        `Fst c  else `Snd c
                   | (_ as c) -> `Snd c)
  in
  bind_solutions
    sita ~exists:binds
    [ `Toplevel_apps toplevel_apps;
      `Or_clauses_with_app_term or_clauses_with_app_term;
      `Other_clauses other_clauses]
    ~f:(fun sita -> function
         | `Toplevel_apps toplevel_apps ->
                solve_application_list
                  expand_count sita ~exists:binds ep ~premise toplevel_apps
         | `Or_clauses_with_app_term or_clauses ->
            eliminate_app_from_or_clause_list
              expand_count sita
              ~exists:binds ep ~premise or_clauses
         | `Other_clauses clauses ->
            Seq.singleton (sita, [], [`Horn ([], Hfl.concat_by_and clauses)] )
       )
            

    
let f sita ~exists:binds ep premise_clauses clause =
  let premise = List.fold_right
                  ~f:Premise.add
                  premise_clauses
                  ~init:Premise.empty
  in
  eliminate_app 0 sita ~exists:binds ep ~premise clause
  |> Seq.concat_map
       ~f:(fun (sita, new_exists, horns) ->
         match pre_check_horns sita ~exists:(new_exists@binds) horns with
         |None -> Seq.empty
         |Some horns -> Seq.singleton (sita, new_exists, horns))

  
