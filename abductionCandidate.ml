module Seq = Base.Sequence
           
type t = {now: BaseLogic.t list
         ;candidates: BaseLogic.t list (* 順番に意味なし、setでもよい *)
           }


let empty = {now = []; candidates = []}
          
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

let filter_unsat_candidate penv candiates =
    let penv_z3 =
    PathEnv.extract_condition penv
    |> List.map (function |`Base e -> e | _ -> invalid_arg "not impl yet")
    |> List.map BaseLogic.to_z3_expr
    |> List.map fst
    in
    List.filter
      (fun condition ->
        let condition_z3 = fst (BaseLogic.to_z3_expr condition) in
        UseZ3.bind_and_list (condition_z3::penv_z3)
        |>UseZ3.is_satisfiable
      )
      candiates


let initialize penv qualifiers ~new_vars t =
  let candidates' =
    match new_vars with
    |[] -> filter_unsat_candidate penv (t.now@t.candidates)
    | _::_ ->
       let new_candidates =
         List.map (Qualifier.gen_formulas penv ~must_include_vars:(S.of_list new_vars)) qualifiers
         |> List.concat
       in
       filter_unsat_candidate penv (new_candidates@t.now@t.candidates)
  in
  {now = [];
   candidates = candidates'}     

  
    
  
