module Seq = Base.Sequence

module type SYNTHESIS = sig
  val gen_b_term:Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.sort -> spec:Hfl.qhorn list 
                 -> Program.b
end

(* 試しに第1級モジュールでパラメータを扱ってみる *)
let generator data_env qualifyer e_depth =
  (module struct

     let gen_e_term ep penv abduction_candidate sort spec =
       GenEterms.f ep penv abduction_candidate sort spec e_depth
       |> Seq.hd
       
       
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
           let cond = AbductionCandidate.get abduction_candidate in
           if cond = [] then Some (Program.PE e)
           else
             let else_cond = BaseLogic.Not (BaseLogic.and_list cond) in
             let penv' = PathEnv.add_condition (`Base else_cond) penv in
             let abduction_candidate = AbductionCandidate.initialize penv' abduction_candidate in
             let b_else =  gen_b_term ep penv' abduction_candidate sort ~spec in
             let open Program in
             Some (PIf ((PredCond (BaseLogic.and_list cond)),
                  (PE e),
                  b_else))
         |None -> None)
   end
          :SYNTHESIS)
         
