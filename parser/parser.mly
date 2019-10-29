%{

open ParseSyntax
open BaseLogic
%}


%token OF // "of"
%token TYPE // "type"
%token FUN
%token FUNCTION
%token ATMARK
%token QUALIFIER
%token LET
%token REC
// attribute
%token PARAM
%token SPECIFICATION
%token REFINEPREDICATE
%token PREDICATE
%token MEASURE
%token TERMINATION

%token NU
%token MU

%token INTSYMBOL
%token BOOLSYMBOL
%token BASE


%token EQUAL
%token NEQUAL
%token NOT
%token AND
%token OR
%token IMPLIES
%token HORNIMPLIES
%token IFF
%token LESS
%token LESS_EQUAL
%token GREATER
%token GREATER_EQUAL
%token MINUS
%token PLUS
%token AST
%token IN
%token IF
%token THEN
%token ELSE
%token MATCH
%token WITH
%token SET
%token ALLOW
%token COLON
%token SEMICOLON
%token QUESTION
%token LPAREN
%token RPAREN
%token LSQBRAC
%token RSQBRAC
%token LCURBRAC
%token RCURBRAC
%token PIPE

%token COMMA
%token VALVAR
%token TRUE
%token FALSE
%token <int> INT

%token <Id.t> ID
%token <Id.t> CAPID
%token <Id.t> MEASUREID
%token EOF

%right prec_clause
%right prec_if
%left NOT AND OR IMPLIES IFF 
%left EQUAL NEQUAL GREATER GREATER_EQUAL LESS LESS_EQUAL
%left PLUS MINUS PLUS_DOT MINUS_DOT IN
%left AST
%right prec_base
%left prec_app


%type < ParseSyntax.t > toplevel
%type < Hfl.sort > sort
%type < Hfl.baseSort > basesort
%type < ParseSyntax.clause > clause
%start toplevel


%%

toplevel:
| qualifierDef toplevel
 { (QualifierDef $1) :: $2 }
 
| dataDef toplevel
 { (DataDef $1) :: $2 }
 
| measureDef toplevel
 { (MeasureDef $1) :: $2 }
 
| refinePredicateDef toplevel
 { (RefinePredicateDef $1) :: $2 }

| predicateDef toplevel
 {  (PredicateDef $1) :: $2 }

| varSpecDec toplevel
 { (VarSpecDec $1) :: $2 }

| goal toplevel
 { (Goal $1) :: $2 }

| EOF
{ [] }



/* **************************************************
   qualifier definition
 ************************************************** */
qualifierDef:
| LET QUALIFIER EQUAL LSQBRAC l = separated_list(SEMICOLON, qualifier) RSQBRAC
  { l }

qualifier:// \x:int. x > 0 など
| FUN args = list(abstArg) ALLOW body = baselogic 
  { Qualifier.make args body }
| LPAREN FUN args = list(abstArg) ALLOW body = baselogic RPAREN
  { Qualifier.make args body }  

abstArg:
| x = ID COLON s = basesort
   { (x, s) }
| LPAREN x = ID COLON s = basesort RPAREN
   { (x, s) }

/* **************************************************
   data type definition
 ************************************************** */
dataDef:
| TYPE i = ID EQUAL cons_defs = nonempty_list(constructorDef)
  { ParseSyntax.{name = i; constructors = cons_defs } }

constructorDef:
| PIPE cons = CAPID
  { ParseSyntax.{name = cons; args = []} }
| PIPE cons = CAPID OF LPAREN arg_sorts = separated_list(AST, basesort) RPAREN
   { ParseSyntax.{name = cons; args = arg_sorts} }
| PIPE cons = CAPID OF arg_sorts = separated_list(AST, basesort) 
   { ParseSyntax.{name = cons; args = arg_sorts} }


%public attribute(X):
| LSQBRAC ATMARK x = X RSQBRAC
  { x }


/* **************************************************
   measure definition
   let [@measure termination] len: list -> int = function ...
 ************************************************** */
measureDef:
| LET attribute(MEASURE) termination = boption(attribute(TERMINATION)) option(REC)
    measure = ID COLON arg_data = ID ALLOW ret_sort = basesort
     EQUAL FUNCTION cases = nonempty_list(measureCase)
  { DataType.{name = measure;
              termination = termination;
	      inputSort = `DataS arg_data;
	      returnSort = ret_sort;
	      matchCases = cases}
  }

measureCase:
| PIPE cons = CAPID args = separated_list(COMMA, ID) ALLOW body = baselogic
  { DataType.{constructor = cons;
              args = args;
              body = body}
   }
| PIPE cons = CAPID LPAREN args = separated_list(COMMA, ID) RPAREN ALLOW body = baselogic
  { DataType.{constructor = cons;
              args = args;
              body = body}
   }   
	      
/* **************************************************
   data predicate definition
   
   let [@refine-predicate] _List (p:int -> bool) = function
         |Cons x xs -> p x && _List p xs
	 |Nil -> true
	 
 ************************************************** */
 
refinePredicateDef:
| LET attribute(REFINEPREDICATE) option(REC) name = ID args = list(predicateArg)
   EQUAL FUNCTION cases = nonempty_list(refineCase)
  { ParseSyntax.{name = name;
                 param = args;
                 cases = cases}
  }

refineCase:
| PIPE cons = CAPID args = separated_list(COMMA, ID) ALLOW body =  clause
  { ParseSyntax.{name = cons; args = args; body = body} }
  
| PIPE cons = CAPID LPAREN args = separated_list(COMMA, ID) RPAREN ALLOW body =  clause
  { ParseSyntax.{name = cons; args = args; body = body} }  


/* **************************************************
  hfl predicate definition
   let[@predicate][@nu] _P (f:int -> bool) (r[@param]:int -> bool) (x:int) =
      x > 0 => (...)
 ************************************************** */
predicateArg:
| LPAREN name = ID is_param = boption(attribute(PARAM)) COLON sort = sort RPAREN
   {ParseSyntax.{name = name;
                 is_param = is_param;
		 sort = sort
		 }
    }


fixpoint:
| NU {Hfl.Nu}
| MU {Hfl.Mu}

predicateDef:
| LET attribute(PREDICATE) fixpoint = option(attribute(fixpoint))
    name = ID args = list(predicateArg) EQUAL body = predicateBody
 { ParseSyntax.{name = name;
                args = args;
		fixpoint = fixpoint;
		body = body}
 }

predicateBody:
| pre = clause HORNIMPLIES body = clause
  { (Some pre, body) }
| body = clause
  { (None, body) }


/* **************************************************
  function specification
   let[@specification sort][@nu] _P (f:int -> bool) (r[@param]:int -> bool) (x:int) =
      x > 0 => (...)
 ************************************************** */

varSpecDec:
| LET fun_name = attribute(specAttribute) fixpoint = option(attribute(fixpoint))
    pred_name = ID args = list(predicateArg) EQUAL body = predicateBody
 { (fun_name, ParseSyntax.{name = pred_name;
                           args = args;
                           fixpoint = fixpoint;
               		   body = body})
 }

specAttribute:
| SPECIFICATION name = ID
   { name }



/* **************************************************
 goal
 ************************************************** */
goal:
| LET id = ID EQUAL QUESTION
  { id }

/* **************************************************
   hfl clause
 ************************************************** */

clause:
| boolClause
  { $1 }
| absClause
  { $1 }

clauseAtom:
| boolClauseAtom { $1 }
| absClause { $1 }

appClause:// application節が clauseとbaselogicの違い
| funName = ID args = appArgs // h B(x) (fun i -> B(i>0)) ..
%prec prec_app 
  { `App (ParseSyntax.{head = funName; args = args}) }


appArgs:
| clauseAtom
%prec prec_app
  { [$1] }
| clauseAtom appArgs
%prec prec_app
  { $1 :: $2 }

boolClause:
| boolClauseAtom
  { $1 }
| baselogic
%prec prec_base
  { `Base $1 }
| boolClauseJoin
 { $1 }


boolClauseJoin:
| boolClauseAtom AND boolClause
%prec prec_clause
  { `And ($1, $3) }
| boolClauseAtom OR boolClause
%prec prec_clause
  { `Or ($1, $3) }

boolClauseAtom:
| appClause
%prec prec_app 
  { $1 }
| LPAREN boolClauseJoin RPAREN
  %prec prec_clause
  { $2 }


absClause:
| LPAREN FUN args = nonempty_list(absArg) ALLOW body = boolClause RPAREN // (fun (x:int) -> x >0)
  { `Abs (args, body) }

absArg:
| LPAREN name = ID COLON sort = sort RPAREN
   { (name, sort) }


/* **************************************************
   sort basesort
 ************************************************** */
basesort:
| BOOLSYMBOL { `BoolS }
| INTSYMBOL { `IntS }
| elm = basesort SET { `SetS elm }
| ID { `DataS $1 }

sort:
| sortAtom
  { $1 }
| arg = sortAtom ALLOW ret = basesort
 { `FunS ([arg], ret) }
| arg = sortAtom AST other =  separated_nonempty_list(AST, sortAtom) ALLOW ret = basesort
 { `FunS (arg::other, ret) }
//| LPAREN args = separated_nonempty_list(AST, sortAtom) RPAREN ALLOW ret = basesort
// { `FunS (args, ret) } 

sortAtom:
| basesort
  { ($1:> Hfl.sort) }
| LPAREN sort = sort RPAREN  
 { sort }

/* **************************************************
   baselogic
 ************************************************** */

baselogicAtom:
| TRUE
  { BaseLogic.Bool true }
| FALSE
  { BaseLogic.Bool false }
| INT
  { BaseLogic.Int $1 }
| LSQBRAC elms= separated_list(COMMA, baselogic) RSQBRAC
  { BaseLogic.Set (ParseSyntax.sort_unfix, elms) }
| VALVAR { Var (ParseSyntax.sort_unfix, Id.valueVar_id) }
| ID { Var (ParseSyntax.sort_unfix, $1) }
| LPAREN baselogic RPAREN { $2 }


baselogic:
| baselogicAtom
   {$1}
| MEASUREID nonempty_list(baselogicAtom)
%prec prec_app 
   { UF (ParseSyntax.sort_unfix, $1, $2) } 
| CAPID list(baselogicAtom)
%prec prec_app 
   { Cons (ParseSyntax.sort_unfix, $1, $2) } 
| IF e1 = baselogic THEN e2 = baselogic ELSE e3 = baselogic
   %prec prec_if
   { If (e1, e2, e3) }
| baselogic AST baselogic
  { Times ($1, $3) }  /* int_mul or set_intersection, decide later*/
| baselogic PLUS baselogic
  { Plus ($1, $3) }   /*int_plus or set_union, decide later*/
| baselogic MINUS baselogic
  { Minus ($1, $3) }  /*int_minus of set_diff, decide later*/
| baselogic EQUAL EQUAL baselogic
  { Eq ($1, $4) }
| baselogic NEQUAL baselogic
  { Neq ($1, $3) }
| baselogic LESS baselogic
  { Lt ($1, $3) }
| baselogic LESS_EQUAL baselogic
  { Le ($1, $3) } /*Le of set_subset, decide later*/
| baselogic GREATER baselogic
  { Gt ($1, $3) }
| baselogic GREATER_EQUAL baselogic
  { Ge ($1, $3) }
| baselogic AND baselogic
  { And ($1, $3) }
| baselogic OR baselogic
  { Or ($1, $3) }
| baselogic IMPLIES baselogic
  { Implies ($1, $3) }
| baselogic IFF baselogic
  { Iff ($1, $3) }
| baselogic IN baselogic
  { Member ($1, $3) }
| MINUS baselogic
  { Neg $2 }
| NOT baselogic
  { Not $2 }
