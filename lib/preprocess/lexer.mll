{
open Parser
open Lexing
let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
    
}

let space = [' ' '\t' '\r']
let newline = ('\r'* '\n')
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']

rule main = parse

| space+
 { main lexbuf }

| newline
 { new_line lexbuf; main lexbuf}

| "(*"               
    { comment lexbuf;
      main lexbuf }

| "(*" space* "ignore" space* "*)"
  { ignore_section lexbuf; main lexbuf }
| "let"
 { LET }
| "rec"
 { REC }
| "exists"
 { EXISTS }
 

 
| "qualifier"
 { QUALIFIER }
| "of"
 { OF }
| "type"
 { TYPE }
| "fun"
 { FUN }
| "function"
 { FUNCTION }

| "if"
 { IF }
| "then"
 { THEN }
| "else"
 { ELSE }


| "not"
 { NOT }
| "int"
  {INTSYMBOL}
| "bool"
  {BOOLSYMBOL}
| "set"
  {SET}

| "@"
 { ATMARK }
| "spec"
 { SPECIFICATION }
| "predicate"
 { PREDICATE }
| "refine-predicate"
 { REFINEPREDICATE }
| "param"
 { PARAM }
| "measure"
 { MEASURE }
| "termination"
 { TERMINATION }
| "nu"
{ NU }
| "mu"
{ MU }
| "in"
{ IN }

| "Base" 
 { BASE }
|"="
 { EQUAL }

| "<>"
 { NEQUAL }
| "&&"
 { AND }
| "||"
 { OR }
 | "==>"
 { HORNIMPLIES }
| "&&&"
 { HORNAND }
| "|||"
 { HORNOR }
| "=>"
 { IMPLIES }
| "<==>"
 { IFF }
| "<"
 { LESS }
| "<<"
  { SUBSET }
| "<="
 { LESS_EQUAL } 
| ">"
 { GREATER }
| ">="
 { GREATER_EQUAL }
| '-'
    { MINUS }
| "--"
   {DIFF}
| '+' 
    { PLUS }
| "++"
   { UNION }
| '*'
    { AST }
| "**"
  {INTERSECTION}
 | "->"
 { ALLOW }
| ":"
 { COLON }
| ";"
 { SEMICOLON }
| "??"
 { QUESTION }
| "("
 { LPAREN }
| ")"
 { RPAREN }
| "["
 { LSQBRAC }
| "]"
 { RSQBRAC }
| "{"
 { LCURBRAC }
| "}"
 { RCURBRAC }
| "|"
 { PIPE }
| ','
 { COMMA }
| '.'
 { DOT }
| "true"
 { TRUE }
| "false"
 { FALSE }
| digit+ as n
 { INT (int_of_string n) }
|eof
 { EOF }
| '_'  lower (digit|lower|upper|'_'|'\'')* as id
 { MEASUREID (Id.of_string_symbol id) }
 
| ('_'|lower) (digit|lower|upper|'_'|'\'')* as id
 { ID (Id.of_string_symbol id) }
| upper (digit|lower|upper|'_'|'\'')* as id
 { CAPID (Id.of_string_symbol id) }
| _
    { failwith
	(Printf.sprintf "unknown token %s near line %d characters %d-%d"
	   (Lexing.lexeme lexbuf)
	   ((Lexing.lexeme_start_p lexbuf).Lexing.pos_lnum)
	   (Lexing.lexeme_start lexbuf)
	   (Lexing.lexeme_end lexbuf)) }

 
and comment = parse
| "*)"
    { () }
| "(*"
    { comment lexbuf;
      comment lexbuf }
| newline
 { new_line lexbuf; comment lexbuf}      
| eof
    { Format.eprintf "warning: unterminated comment@." }
| _
    { comment lexbuf }

and ignore_section = parse
| "(*" space* "endignore" space* "*)"
 { () }
|eof
    { Format.eprintf "warning: unterminated ignore section@." }
| newline
 { new_line lexbuf; ignore_section lexbuf}          
| _
  { ignore_section lexbuf }