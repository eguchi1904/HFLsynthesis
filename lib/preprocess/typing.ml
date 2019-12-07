open ParseSyntax
open Extensions

exception TypeError of string

let rec cons_gen env e =
  let open BaseLogic in
  match e with
  |Bool b -> Bool b, (BoolS, [])
  |Int i-> Int i, (IntS, [])
  |Set (_,[]) ->let unknown_s = UnknownS (Id.genid "emps") in
                Set (unknown_s,[]), (SetS ( unknown_s), [])
  |Set (_,es) ->
    let es', sort_constrain =
      List.split (List.map (cons_gen env) es) in 
    let (s1::sorts),constrainlist = List.split sort_constrain in
    let constrain = List.concat constrainlist in
    let new_c = List.map (fun s -> (s1,s)) sorts in (* 各elemが同じ *)
    Set (s1, es'), (SetS s1, new_c@constrain)

  |Var (_, i) when M.mem i env ->
    (match M.find i env with
     | `BoolS | `IntS | `DataS _ | `SetS _ as base_sort ->
        let bsort = Hfl.to_baseLogic_sort base_sort in
        Var (bsort, i), (bsort, [])
     | sort ->
        let mes = Printf.sprintf "%s should have base sort, but have %s"
                                 (Id.to_string_readable i)
                                 (Hfl.sort2string sort)
        in
        raise (TypeError mes))
   


  |Unknown _ -> assert false
              
  |Cons (_, i, []) when M.mem i env ->
    (match M.find i env with    
     | `DataS data ->
        let bsort = DataS (data,[]) in
          Cons (bsort, i, []), (bsort, [])
     | sort ->
        let mes = Printf.sprintf
                      "%s expected sclar constructor, but have sort %s, "
                      (Id.to_string_readable i)
                      (Hfl.sort2string sort) in
        raise (TypeError mes)
    )              
  |Cons (_, i, es) when M.mem i env->
    let es', sort_constrain = List.split (List.map (cons_gen env) es) in
    let es_sorts, constrainlist = List.split sort_constrain in
    let constrain = List.concat constrainlist in
    (match M.find i env with
     | `FunS (arg_sorts, `DataS data) ->
        if List.length arg_sorts <> List.length es then
          let mes = Printf.sprintf
                      "%s's expected to have %d arguments, but got %d"
                      (Id.to_string_readable i)
                      (List.length arg_sorts)
                      (List.length es)
          in
          raise (TypeError mes)
        else
          let new_c =
            List.map2
              (fun elms reqs ->
                match reqs with
                | `BoolS | `IntS | `DataS _ | `SetS _ as base_sort ->
                   (elms, Hfl.to_baseLogic_sort base_sort)
                | _ -> assert false)
              es_sorts
              arg_sorts
          in
          let bsort = DataS (data,[]) in
          Cons (bsort, i, es'), (bsort,(new_c@constrain))
     | sort ->
        let mes = Printf.sprintf
                    "constructor %s has sort %s, bu should be return data type"
                    (Id.to_string_readable i)
                    (Hfl.sort2string sort)
        in
        raise (TypeError mes))
        

  |UF (_, i, es)  when M.mem i env -> (* measureの適用 *)
    let es', sort_constrain = List.split (List.map (cons_gen env) es) in
    let es_sorts, constrainlist = List.split sort_constrain in
    let constrain = List.concat constrainlist in
    (match M.find i env with
     | `FunS (arg_sorts, basesort) ->
        if List.length arg_sorts <> List.length es then
          let mes = Printf.sprintf
                      "%s's expected to have %d arguments, but got %d"
                      (Id.to_string_readable i)
                      (List.length arg_sorts)
                      (List.length es)
          in
          raise (TypeError mes)
        else
          let new_c =
            List.map2
              (fun elms reqs ->
                match reqs with
                | `BoolS | `IntS | `DataS _ | `SetS _ as base_sort ->
                   (elms, Hfl.to_baseLogic_sort base_sort)
                | _ -> assert false)
              es_sorts
              arg_sorts
          in
          let bsort = Hfl.to_baseLogic_sort basesort in
          UF (bsort, i, es'), (bsort,(new_c@constrain))
     | _ ->
        assert false
    )

  |Var (_,i) | UF (_, i, _) |Cons (_, i,_) ->
    raise (TypeError ("unbound value "^(Id.to_string_readable i)))    

  |If (e1,e2,e3) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let e3',(s3,c3) = cons_gen env e3 in
    let new_c = [(s1,BoolS);(s2,s3)] in
    If (e1', e2', e3'), (s2, new_c@c1@c2@c3)

  |Times (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Times (e1',e2'), (IntS, consrain')
  
    
    
  |Plus (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Plus (e1',e2'), (IntS, consrain')

  |Minus (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Minus (e1',e2'), (IntS, consrain')
  

  |Eq (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Eq (e1', e2'), (BoolS, consrain')

  |Neq (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Neq (e1', e2'), (BoolS, consrain')

  |Lt (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(s1, IntS)::(c1@c2) in
    Lt (e1', e2'), (BoolS, consrain')

  |Le (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(s1, IntS)::(c1@c2) in
    Le (e1',e2'), (BoolS,consrain')
    

  |Gt (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(s1, IntS)::(c1@c2) in
    Gt (e1', e2'), (BoolS, consrain')

  |Ge (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(s1, IntS)::(c1@c2) in
    Ge (e1', e2'), (BoolS, consrain')

  |And (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(s1,BoolS)::(c1@c2) in
    And (e1', e2'), (BoolS, consrain')

  |Or (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(s1,BoolS)::(c1@c2) in
    Or (e1', e2'), (BoolS, consrain')

  |Implies (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(s1,BoolS)::(c1@c2) in
    Implies (e1', e2'), (BoolS, consrain')

  |Iff (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (s1,s2)::(s1,BoolS)::(c1@c2) in
    Iff (e1', e2'), (BoolS, consrain')

  |Member (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let consrain' = (SetS s1,s2)::(c1@c2) in
    Member (e1', e2'), (BoolS, consrain')

  |Neg e1 ->
    let e1',(s1,c1) = cons_gen env e1 in
    let consrain' = (s1,IntS)::c1 in
    Neg e1', (IntS, consrain')

  |Not e1 ->
    let e1',(s1,c1) = cons_gen env e1 in
    let consrain' = (s1,BoolS)::c1 in
    Not e1', (BoolS, consrain')

  |Union (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let unknown_s = UnknownS (Id.genid "elm") in
    let consrain' = (s1,s2)::(s1,SetS unknown_s)::(c1@c2) in
    Union (e1', e2'), (s1, consrain')

  |Intersect (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let unknown_s = UnknownS (Id.genid "elm") in
    let consrain' = (s1,s2)::(s1,SetS unknown_s)::(c1@c2) in
    Intersect (e1', e2'), (s1, consrain')

  |Diff (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let unknown_s = UnknownS (Id.genid "elm") in
    let consrain' = (s1,s2)::(s1,SetS unknown_s)::(c1@c2) in
    Diff (e1', e2'), (s1, consrain')

  |Subset (e1, e2) ->
    let e1',(s1,c1) = cons_gen env e1 in
    let e2',(s2,c2) = cons_gen env e2 in
    let unknown_s = UnknownS (Id.genid "elm") in
    let consrain' = (s1,s2)::(s1,SetS unknown_s)::(c1@c2) in
    Subset (e1', e2'), (s1, consrain')
    
  |All _ |Exist _ -> assert false    

                     
let rec g_clause_abs env (`Abs (args, body)) sort :abstClause=
  let env' = M.add_list args env in
  `Abs (args, g_clause env' body `BoolS)  
                     
and g_clause env (c:clause) sort=
  match c with
  | `Base e ->
     `Base (g_base env e sort)
  | `Abs _ as abs-> (g_clause_abs env  abs sort :> clause)
  | `App {head = head; args= cs} when sort = `BoolS ->
     (match M.find_opt head env with
      |Some (`FunS (args, `BoolS)) ->
        if List.length args <> List.length cs then
          let mes = Printf.sprintf
                      "%s's expected to have %d arguments, but got %d"
                      (Id.to_string_readable head)
                      (List.length args)
                      (List.length cs)
          in
          raise (TypeError mes)
        else
          `App {head = head;
                args = List.map2 (g_clause env) cs args}
      |Some (`FunS (_, _)) -> assert false (* bool以外を返す術後は定義段階でerrorになるはず *)
      |Some sort ->
        let mes = Printf.sprintf
                    "%s should have function sort"
                    (Id.to_string_readable head)
        in
        raise (TypeError mes)
      |None ->
        let mes = Printf.sprintf
                    "unbound value %s"
                    (Id.to_string_readable head)
        in
        raise (TypeError mes))
  | `App {head = head; args= cs} ->
        let mes = Printf.sprintf
                    "expected %s but application term is bool"
                    (Hfl.sort2string sort)
        in
        raise (TypeError mes)
        
  | `RData (rdata, cs, c)  when sort = `BoolS ->
     (match M.find_opt rdata env with
      |Some (`FunS (args, `BoolS)) ->
        if List.length args <> (List.length cs + 1) then
          let mes = Printf.sprintf
                      "%s's expected to have %d arguments, but got %d"
                      (Id.to_string_readable rdata)
                      (List.length args)
                      (List.length cs)
          in
          raise (TypeError mes)
        else
          let cs_sorts, c_sort = List.split_tail args in
          `RData (rdata,
                  List.map2 (g_clause_abs env) cs cs_sorts,
                  g_clause env c c_sort)
      |Some (`FunS (args, _)) -> assert false (* bool以外を返す術後は定義段階でerrorになるはず *)
      |Some sort ->
        let mes = Printf.sprintf
                    "%s should have function sort"
                    (Id.to_string_readable rdata)
        in
        raise (TypeError mes)
      |None ->
        let mes = Printf.sprintf
                    "unbound value %s"
                    (Id.to_string_readable rdata)
        in
        raise (TypeError mes))
     | `RData _ ->
        let mes = Printf.sprintf
                    "expected %s but application term is bool"
                    (Hfl.sort2string sort)
        in
        raise (TypeError mes)

     | `Or (c1, c2) when sort = `BoolS->
        `Or (g_clause env c1 `BoolS, g_clause env c2 `BoolS)
     | `And (c1, c2) when sort = `BoolS ->
        `And (g_clause env c1 `BoolS, g_clause env c2 `BoolS)
     | `Or _| `And _  ->
        let mes = Printf.sprintf
                    "expected %s but Or/And term is bool"
                    (Hfl.sort2string sort)
        in
        raise (TypeError mes)


and g_base env e sort =
  let sort = match sort with
    | `IntS | `DataS _ | `BoolS | `SetS _ as sort -> sort
    | _ ->
       let mes = Printf.sprintf 
                   "%s expected to have base sort but have %s"
                   (BaseLogic.p2string e)
                   (Hfl.sort2string sort)
       in
       raise (TypeError mes)
  in
  let (e', (bsort, const)) = cons_gen env e in
  let sita = BaseLogic.unify_sort const M.empty in
  let sita' =
    try BaseLogic.unify_sort
          [(bsort, Hfl.to_baseLogic_sort sort)]
          sita
    with
      BaseLogic.Unify_Err ->
      let bsort' =  BaseLogic.sort_subst sita bsort in      
      let mes = Printf.sprintf
                  "%s expected to have %s, but have %s"
                  (BaseLogic.p2string e)
                  (Hfl.sort2string sort)
                  (Hfl.sort2string ((Hfl.of_baseLogic_sort bsort'):>Hfl.sort))
    in
    raise (TypeError mes)
  in
  let e'' = BaseLogic.sort_subst2formula sita' e' in
  e''
                 
  
let g_qualifiers env q =
  let (args, body) = Qualifier.reveal q in
  let args' = (args:> (Id.t  * Hfl.sort) list) in
  let env' = M.add_list args' env in
  let body' = g_base env' body `BoolS in
  Qualifier.make args body'


let g_measure_case env data out_sort
                   ({constructor = cons; args = caseargs; body = body}:formulaCase)
    :formulaCase
  =
  let out_sort = (out_sort:>Hfl.sort) in
  match M.find_opt cons env with
  | Some (`DataS data') when data' = data->
     if caseargs <> [] then
       raise (TypeError
                ((Id.to_string_readable cons)^
                   "is a scalar constructor, but this pattern havs arguments"))
     else
       {constructor = cons;
                 args = caseargs;
                 body = g_base env body out_sort}
  | Some (`FunS (arg_sort, `DataS data')) when data = data' ->
     if List.length arg_sort <> List.length caseargs then
       let mes = Printf.sprintf
                   "%s require %d argument, but this pattern has %d args"
                   (Id.to_string_readable cons)
                   (List.length arg_sort)
                   (List.length caseargs)
       in
       raise (TypeError mes)
     else
       let env' = M.add_list2 caseargs arg_sort env in
       let body' = g_base env' body out_sort in
       DataType.{constructor = cons;
                 args = caseargs;
                 body = body'}

  |Some sort ->
    let mes = Printf.sprintf
                "constructor %s should return %s"
                (Id.to_string_readable cons)
                (Id.to_string_readable data)
    in
    raise (TypeError mes)
    
  |None ->
    let mes = Printf.sprintf
                " unbound contrucor %s" (Id.to_string_readable cons)
    in
    raise (TypeError mes)

    
let g_refine_case env data ({name = cons; args = caseargs; body = body}:refineCase) =
    match M.find_opt cons env with
  | Some (`DataS data') when data' = data->
     if caseargs <> [] then
       raise (TypeError
                ((Id.to_string_readable cons)^
                   "is a scalar constructor, but this pattern havs arguments"))
     else
       {name = cons;
        args = caseargs;
        body = g_clause env body `BoolS}
  | Some (`FunS (arg_sort, `DataS data')) when data = data' ->
     if List.length arg_sort <> List.length caseargs then
       let mes = Printf.sprintf
                   "%s require %d argument, but this pattern has %d args"
                   (Id.to_string_readable cons)
                   (List.length arg_sort)
                   (List.length caseargs)
       in
       raise (TypeError mes)
     else
       let env' = M.add_list2 caseargs arg_sort env in
       let body' = g_clause env' body `BoolS in
       DataType.{name = cons;
                 args = caseargs;
                 body = body'}

  |Some _ ->
    let mes = Printf.sprintf
                "constructor %s should return %s"
                (Id.to_string_readable cons)
                (Id.to_string_readable data)
    in
    raise (TypeError mes)
    
  |None ->
    let mes = Printf.sprintf
                " unbound contrucor %s" (Id.to_string_readable cons)
    in
    raise (TypeError mes)
                                                       
    
let infer_sort_from_case env cases =
  match cases with
  |[] -> assert false
  |(case:refineCase)::_ ->
    let cons = case.name in
    match M.find_opt cons env with
    | Some `DataS data |Some (`FunS (_, `DataS data)) ->
       `DataS data
    |_ -> assert false
        

let sort_of_predicate (predicate_def:predicateDef) =
  let args = List.map
                    (fun (arg:predicateArg) -> arg.sort)
                    predicate_def.args
  in
  `FunS (args, `BoolS)
  
        
let g_predicate_def env predicate_def = 
  let predicate_sort = sort_of_predicate predicate_def in
  let {name = name;
       args = predicate_args;
       fixpoint = fixpoint_opt;
       exists = exists;
       body = body}
    = predicate_def
  in
  let arg_sorts = List.map
                    (fun (arg:predicateArg) ->
                      (arg.name, arg.sort))
                    predicate_args
  in
  let env' = M.add name predicate_sort env 
             |> M.add_list arg_sorts
             |> M.add_list (exists:> (Id.t * Hfl.sort) list)
  in
  let body' = match body with
    |(Some c1), c2 ->
      (Some (g_clause env' c1 `BoolS)), g_clause env' c2 `BoolS
    |None, c2 ->
      (None, g_clause env' c2 `BoolS)
  in
  {name = name;
   args = predicate_args;
   fixpoint = fixpoint_opt;
   exists = exists;   
   body = body'}
     
    
  
  
  
let rec g acc env = function
  |QualifierDef qualifiers :: other->
    g
      (acc@[(QualifierDef (List.map (g_qualifiers env) qualifiers))])
      env
      other
   
  |DataDef typedef :: other->
    let data = typedef.name in
    let constructor_sort_list =
      List.map
        (fun (cons:constructor) ->
          if cons.args = [] then
            (cons.name, `DataS data)
          else
            (cons.name, `FunS ((cons.args:>Hfl.sort list), `DataS data)))
        typedef.constructors
    in
    let env' = M.add_list constructor_sort_list env in
    g (acc@[DataDef typedef]) env' other

  |MeasureDef {name = name;
               termination = terminaion;
               inputSort = `DataS data;
               returnSort = out_sort;
               matchCases = cases} :: other ->
    
    let env' = M.add name (`FunS ([`DataS data], out_sort)) env in
    let cases' = List.map (g_measure_case env' data out_sort) cases in
    let measure_def' =
      {name = name;
       termination = terminaion;
       inputSort = `DataS data;
       returnSort = out_sort;
       matchCases = cases'} in
    g (acc@[MeasureDef measure_def']) env' other
 
  |RefinePredicateDef {name = name;
                       param = predicate_args;
                       cases = cases}:: other ->
    
    let `DataS data = infer_sort_from_case env cases   in
    let arg_sorts = List.map
                      (fun (arg:predicateArg) ->
                        (arg.name, arg.sort))
                      predicate_args
    in
    let predicate_sort =
      `FunS ((List.map snd arg_sorts)@[`DataS data], `BoolS)
    in
    let env' = M.add name predicate_sort env in
    let env'' = M.add_list arg_sorts env' in
    let cases' = List.map (g_refine_case env'' data) cases in
    let refine_predicate_def' = {name = name;
                                 param = predicate_args;
                                 cases = cases'}
    in
    g (acc@[RefinePredicateDef refine_predicate_def']) env' other

  |PredicateDef predicate_def
   :: other ->
    let predicate_def' = g_predicate_def env predicate_def in
    let predicate_sort = sort_of_predicate predicate_def in
    let env' = M.add predicate_def.name predicate_sort env in
    g (acc@[PredicateDef predicate_def']) env' other

  |VarSpecDec (var_name, predicate_def) :: other ->
    let predicate_def' = g_predicate_def env predicate_def in
    let predicate_sort = sort_of_predicate predicate_def in
    let env' = env
               |> M.add predicate_def.name predicate_sort
    in
    g (acc@[VarSpecDec (var_name, predicate_def')]) env' other


  |Goal id :: other-> g (acc@[Goal id]) env other

  |[] -> acc, env
  
  
let f t = g [] M.empty t
