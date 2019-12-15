open Id
open BaseLogic
open Hfl
open Synthesis
open PathEnv
open AbductionCandidate
open AppElimination
open SolveEquality
   
let e_term_max_size = 5
let scrutinee_max_size = 3


let syntheis synthesizer ep (var, (pathenv, sort)) =
  match Hfl.Equations.find ep var with
  |Some (None, fhorn) ->
    let st = Sys.time () in    
    (try
       let program = synthesizer ep pathenv var sort ~spec:fhorn in
       let ed = Sys.time () in
       (Format.printf "synthesis SUCSESS:\ntime:%f\nz3 time:%f\niteration:%d\n\n\n@."
                      (ed -. st)
                      (!UseZ3.z3_t)
                      (!GenEterms.constraint_count)
       )
       ;
       (Format.printf "%s\n\n@." (Program.to_string program))
     with
     |Invalid_argument mes ->
       let ed = Sys.time () in       
       Format.printf "synthesize FAIL: *%s\ntime:%f\ntime of z3:%f\niteration:%d
                      @."
                     mes
                     (ed -. st)
                     (!UseZ3.z3_t)
                      (!GenEterms.constraint_count)       
    )
  |Some _ -> assert false
  |None -> assert false




let f () =
  let file = ref "" in
  Arg.parse
    []
    (fun s -> file := s)
    ("hfl synthesis");  
  let data_env, ep, qualifiers, goals = Preprocess.f !file in
  let module Synthesizer =
    (val (Synthesis.generator data_env qualifiers ~e_max:e_term_max_size) ~scrutinee_max_size)
  in
  List.iter (syntheis Synthesizer.f ep) goals 


