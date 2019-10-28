{
open Parser
}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']

rule main = parse

| space+
 { main lexbuf }

| "\n"
 { Lexing.new_line lexbuf;NEWLINE}

| "(*"               
    { comment lexbuf;
      token lexbuf }
| "let"
 { LET }
 | "rec"
 { REC }

 
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


| "Base" 
 { BASE }
 
| "!="
 { NEQUAL }
| "&&"
 { AND }
| "||"
 { OR }
| "==>"
 { IMPLIES }
| "<==>"
 { IFF }
| "<"
 { LESS }
| "<="
 { LESS_EQUAL } 
| ">"
 { GREATER }
| ">="
 { GREATER_EQUAL }
| '-'
    { MINUS }
| '+' 
    { PLUS }
| '*'
    { AST }
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
| "_v"
 { VALVAR } 
| "true"
 { TRUE }
| "false"
 { FALSE }
| digit+ as n
 { INT (int_of_string n) }
|eof
 { EOF } 
| (lower|'_') (digit|lower|upper|'_'|'\'')* as id
 { ID id }
| upper (digit|lower|upper|'_'|'\'')* as id
 { CAPID id }
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
| eof
    { Format.eprintf "warning: unterminated comment@." }
| _
    { comment lexbuf }