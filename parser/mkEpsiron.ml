open ParseSyntax


let to_hfl_clause:predicateDef M.t -> clause -> Hfl.clause =
  (fun pmap c -> assert false)

let separate_params: predicateArg list -> (Id.t * Hfl.abstSort) list * (Id.t * Hfl.sort) list =
  (fun predicate_args -> assert false)

let align_by_arg: Id.t list -> Hfl.clause -> Hfl.clause list =
  (fun args clause -> assert false)
   

let mk_fhorn (pmap: predicateDef M.t) (predicate_def:predicateDef) :Hfl.fhorn=
  let params, args = separate_params predicate_def.args in  
  match predicate_def.body with
  |(Some c1, c2) ->
    let c1 = to_hfl_clause pmap c1 in
    let c2 = to_hfl_clause pmap c2 in
    let arg_cs = align_by_arg (List.map fst args) c1 in
    {params = params;
     args = args;
     body = `Horn (arg_cs, c2)}
  |None, c2 ->
    let c2 = to_hfl_clause pmap c2 in
    {params = params;
     args = args;
     body = `Horn ([], c2)}    
    
  

(* let g ep t = *)
(*   match t with *)
(*   |(PredicateDef predicate_def ) :: other -> *)
    
