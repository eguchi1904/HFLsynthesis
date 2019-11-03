open Id
open BaseLogic
open Hfl
open Synthesis
open PathEnv
open AbductionCandidate

             

let _ =
  let file = ref "" in
  Arg.parse
    []
    (fun s -> file := s)
    ("hfl synthesis");  
  let data_env, ep, goals = Preprocess.f !file in
  print_string "hello"

