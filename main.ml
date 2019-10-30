open Id
open BaseLogic
open Hfl
open Synthesis
open PathEnv
open AbductionCandidate

let print_position outx lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:line %d:character %d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  let open Lexing in  
  try Parser.toplevel Lexer.main lexbuf with
  | Parser.Error ->
     Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)
             
let parse filepath =
  let lexbuf =  let inchan = open_in filepath in
                Lexing.from_channel inchan
  in
  parse_with_error lexbuf   

let _ =
  let file = ref "" in
  Arg.parse
    []
    (fun s -> file := s)
    ("hfl synthesis");
  let presyntax = parse !file 
  in
  
  print_string "hello"

