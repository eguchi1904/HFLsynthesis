module List = Base.List


module Premise:sig
  type t

  val show: t -> Hfl.clause list

  val add:Hfl.clause -> t -> t

  val show_equality_premise: t -> (BaseLogic.t * BaseLogic.t ) list



end = struct

  type t = {generalPremise:Hfl.clause list;
            equalityPremise:(BaseLogic.t * BaseLogic.t) list (* subset *)
           }

  let show t = t.generalPremise

  let add c t =
    {generalPremise = c::t.generalPremise;
     equalityPremise = match c with
                       | `Base BaseLogic.Eq (e1, e2) ->
                          (e1, e2)::t.equalityPremise
                       | _ ->
                          t.equalityPremise
    }

  let show_equality_premise t = t.equalityPremise
                         
end

    
(* うーん *)
let decompose_application_terms_implication_by_monotonicity:
      Hfl.application -> Hfl.application
      -> (BaseLogic.t * BaseLogic.t * BaseLogic.sort) list 
         * ((Hfl.clause * Hfl.clause) list )=
  (fun {head = head; params = params1; args = args1}
       {head = head'; params = params2; args = args2} ->
    if head <> head' then invalid_arg " docompose "
    else
      
      assert false
  )

let solve_inequality_constraints:
      exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> PathEnv.t
      -> premise:Premise.t
      ->  (BaseLogic.t * BaseLogic.t * BaseLogic.sort) list 
          * ((Hfl.clause * Hfl.clause) list )
      -> Hfl.clause M.t option =
  (fun ~exists:binds ep penv ~premise (eq_cons, ineq_cons) ->
    let equality_premise = Premise.show_equality_premise premise in
    match SolveEquality.f ~exists:binds ~equality_premise eq_cons with
    |None -> None
    |Some sita ->
      
    assert false
  )

(* 結論からapplicationのtermを消し去りたい。 *)
(* rDataはいらない、ということにしようとり会えず *)
let solve_application:
      exists:(Id.t * Hfl.sort) list
      -> Hfl.Equations.t
      -> PathEnv.t
      -> premise:Premise.t
      -> Hfl.application
      -> Hfl.clause M.t option
  =
  (fun ~exists:binds ep penv ~premise ({head = head;_} as app) ->
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
          decompose_application_terms_implication_by_monotonicity premise_app app
        )
    in
    List.find_map
      ineq_constraints
      ~f:(solve_inequality_constraints ~exists:binds ep penv ~premise)
  )

       
  
