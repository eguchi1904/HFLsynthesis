module Seq = Base.Sequence
open Extensions
           
type t = {now: BaseLogic.t list
         ;candidates: BaseLogic.t list (* 順番に意味なし、setでもよい *)
           }


let empty = {now = []; candidates = []}

let to_string {now = cond; candidates = future} =
  let cond_str = List.map BaseLogic.p2string cond
                 |> String.concat ";"
  in
  let future_str = List.map BaseLogic.p2string future
                 |> String.concat ";"
  in
  "("^"["^cond_str^"]"^" (< ["^future_str^"] )"
          
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
    (* |> List.map (function |`Base e -> e | _ -> assert false) *)
    |> List.map UseZ3.clause_to_z3_expr
    |> List.map fst
    in
    List.filter
      (fun condition ->
        let condition_z3 = fst (UseZ3.convert condition) in
        UseZ3.bind_and_list (condition_z3::penv_z3)
        |>UseZ3.is_satisfiable
      )
      candiates


let filter penv candidates =
  List.uniq_f BaseLogicEq.f candidates
  |> filter_unsat_candidate penv

let initialize data_env penv qualifiers ~new_vars t =
  let candidates' =
    match new_vars with
    |[] -> filter_unsat_candidate penv (t.now@t.candidates)
    | _::_ ->
       let new_candidates =
         List.map (Qualifier.gen_formulas data_env penv ~must_include_vars:(S.of_list new_vars)) qualifiers
         |> List.concat
       in
       filter penv (new_candidates@t.now@t.candidates)
  in
  {now = [];
   candidates = candidates'}     

  
    
  
