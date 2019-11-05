open Id
open BaseLogic
open Hfl
open Synthesis
open PathEnv
open AbductionCandidate

let application_max_depth = 3


let syntheis synthesizer ep (var, (pathenv, sort)) =
  match Hfl.Equations.find ep var with
  |Some (None, fhorn) ->
    let program = synthesizer ep pathenv var sort ~spec:fhorn in
    Format.printf "%s\n\n@." (Program.to_string program)
  |Some _ -> assert false
  |None -> assert false

  

let _ =
  let file = ref "" in
  Arg.parse
    []
    (fun s -> file := s)
    ("hfl synthesis");  
  let data_env, ep, qualifiers, goals = Preprocess.f !file in

  let module Synthesizer =
    (val (Synthesis.generator data_env qualifiers application_max_depth))
  in
  List.iter (syntheis Synthesizer.f ep) goals 


