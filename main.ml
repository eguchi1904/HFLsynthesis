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
  let inchan = open_in !file in
  let presyntax =(Parser.toplevel
                    Lexer.main
                    (Lexing.from_channel inchan))
  in
  print_string "hello"

