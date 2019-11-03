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


let rec extract_predicate_def pmap t =
  let open ParseSyntax in
  match t with
  |DataDef _ :: other |MeasureDef _ :: other |RefinePredicateDef _ :: other
   |Goal _ :: other |QualifierDef _ :: other
   ->
    extract_predicate_def pmap other
  |PredicateDef predicate_def :: other ->
    let name = predicate_def.name in
    extract_predicate_def (M.add name predicate_def pmap) other

  |VarSpecDec (_, predicate_def) :: other ->
    let name = predicate_def.name in
    extract_predicate_def (M.add name predicate_def pmap) other

  |[] -> pmap


  
  

    
let f filepath =
  let syntax, sort_env = parse filepath
                         |> Alpha.f (* alpha変換 *)
                         |> Typing.f (* type check/infer *)
  in
  let pmap = extract_predicate_def M.empty syntax in
  let data_env = MkDataTypeEnv.f pmap sort_env syntax in
  let ep = MkHflEquation.f data_env pmap syntax in
  let goals = MkSynthesisGoals.f data_env sort_env syntax in
  data_env, ep, goals
  
  
  
  
