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
