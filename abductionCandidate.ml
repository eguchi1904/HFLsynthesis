module Seq = Base.Sequence
           
type t = {now: BaseLogic.t list
         ;candidates: BaseLogic.t list (* 順番に意味なし、setでもよい *)
           }

let get t = t.now


let strengthen t =
  Seq.unfold_step
    ~init:([], t.candidates)              
    ~f:(function
        |(consumued, cond::future_candidates) ->
          Seq.Step.Yield({now        = cond::t.now
                         ;candidates = consumued@future_candidates},
                         (cond::consumued, future_candidates)
                        )
        |(_, []) ->
          Seq.Step.Done)

let initialize penv t =
  let penv_z3 =
    PathEnv.extract_condition penv
    |> List.map (function |`Base e -> e | _ -> invalid_arg "not impl yet")
    |> List.map BaseLogic.to_z3_expr
    |> List.map fst
  in
  let candidates' =
    List.filter
      (fun condition ->
        let condition_z3 = fst (BaseLogic.to_z3_expr condition) in
        UseZ3.bind_and_list (condition_z3::penv_z3)
        |>UseZ3.is_satisfiable
      )
      (t.now@t.candidates)
  in
  {now = [];
   candidates = candidates'}
  
  
