let sort_unfix = BaseLogic.DataS (Id.genid_const "unfix", [])



type constructor = {name:Id.t;
                    args:Hfl.baseSort list (* (int *  ) -> *)
                   }
type typedef = {name: Id.t
               ;constructors: constructor list}
                 


type predicateArg =
  {name: Id.t;
   is_param: bool;
   sort: Hfl.sort}

  
(* Hfl.clauseとapplicationの部分が違う。parameter等の区別なし。HFl自体もそれで良いのでは？
*)
type  clause = (*\psi(x,y): predicate type formula *)
  [ `Base of BaseLogic.t
  | `Abs of ((Id.t * Hfl.sort) list * clause)(* 1階の場合は使わない *)           
  | `App of application
  | `RData of Id.t * abstClause list * clause (* List (\x.x>0) _v みたいな述語。 実装上特別扱い*)
  (* |Unknown of Id.t * sort  (\* unknown predicate *\) *)
  | `Or of clause * clause
  | `And of clause * clause
  ]
  and application =  {head:Id.t;
                      args:clause list}

  and  abstClause = [`Abs of (Id.t * Hfl.sort) list * clause]
                  


  
type predicateDef = (* F x =mu \phi(x) => \phi(x, F) の形*)
  {name: Id.t;
   args: predicateArg list;
   fixpoint: Hfl.fixOp option;
   body: clause option * clause
  }
         

type refineCase = {name:Id.t;
                   args:Id.t list;
                   body:clause}
                
type refinePredicate =  {name: Id.t;
                         param: predicateArg list;
                         cases: refineCase list}
                        

type elm =
  | QualifierDef of Qualifier.t list
  | DataDef of typedef
  | MeasureDef of DataType.measure
  | RefinePredicateDef of refinePredicate
  | PredicateDef of predicateDef             
  | VarSpecDec of (Id.t * predicateDef)
  | Goal of Id.t


type t = elm list




       
let separete_params_from_application_args
    :predicateArg list -> Hfl.clause list -> Hfl.abstClause list * Hfl.clause list = 
  (fun predicate_args cs ->
  (assert (List.length predicate_args  = List.length cs));
  List.fold_right2
    (fun predicate_arg clause (acc_param, acc_arg) ->
      if predicate_arg.is_param then
        match clause with
        | `Abs _ as abs_clause -> (abs_clause::acc_param, acc_arg)
        | _ -> assert false
      else
        (acc_param, clause::acc_arg)
    )
    predicate_args
    cs
    ([], [])
  )


let rec to_hfl_clause_abs pmap  (`Abs (args, c)) =  `Abs (args, to_hfl_clause pmap c)
  
and to_hfl_clause:predicateDef M.t -> clause -> Hfl.clause =
  (fun pmap c ->
    match c with
    | `Abs _ as abs_c -> (to_hfl_clause_abs pmap abs_c:>Hfl.clause)
    | `Base base -> `Base base
    | `App {head = head; args = cs} ->
       let hfl_cs = List.map (to_hfl_clause pmap) cs in
       (match M.find_opt head pmap with
        |Some head_def ->
          let params, args =
            separete_params_from_application_args
              head_def.args
              hfl_cs
          in
          `App {head = head; params = params; args = args}
        |None -> assert false)
  
    | `RData (id, abst_cs, c) ->
       `RData (id,
               List.map (to_hfl_clause_abs pmap) abst_cs,
               to_hfl_clause pmap c)

    | `Or (c1, c2) ->
       `Or (to_hfl_clause pmap c1,
            to_hfl_clause pmap c2)

    | `And (c1, c2) ->
       `And (to_hfl_clause pmap c1,
            to_hfl_clause pmap c2)
  )
          
          

let separate_params: predicateArg list -> (Id.t * Hfl.abstSort) list * (Id.t * Hfl.sort) list =
  (fun predicate_args ->
    List.fold_right
      (fun predicate_arg (acc_param, acc_args) ->
        if predicate_arg.is_param then
          match predicate_arg.sort with
          |`FunS (_, `BoolS) as abs_sort ->
             ((predicate_arg.name, abs_sort)::acc_param, acc_args)
          | _ -> assert false
        else
          (acc_param, (predicate_arg.name, predicate_arg.sort)::acc_args)
      )
      predicate_args
   ([], [])
  )

let rec align_by_arg_rec args cs =
  match args with
  |_::other_args ->
    let x_cs, other_cs =
      List.partition
        (fun c ->               (* cにothre_argsが出現しない *)
          List.for_all
            (fun y -> not (S.mem y (Hfl.fv c)))
         other_args
        )
        cs
    in
    let x_clause = Hfl.concat_by_and x_cs in
    x_clause::(align_by_arg_rec other_args other_cs)
  |[] -> []
    
         

let align_by_arg: Id.t list -> Hfl.clause -> Hfl.clause list =
  (fun args clause ->
    let cs = Hfl.separate_by_and clause in
    align_by_arg_rec args cs
  )


  

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

     

let extract_data_defs (t:t) =
  List.fold_right
    (fun elm acc ->
      match elm with
      |DataDef typedef -> typedef::acc
      |_ -> acc)
    t
    []

let extracet_cons_env (t:t) = 
    List.fold_right
    (fun elm acc ->
      match elm with
      |DataDef {name = data_name; constructors = constructors} ->
        let constructor_sort_list = 
          List.map
            (fun (cons:constructor) ->
              if cons.args = [] then
                (cons.name, `DataS data_name)
              else
                (cons.name, `FunS ((cons.args:>Hfl.sort list), `DataS data_name)))
          constructors
        in
        M.add_list constructor_sort_list acc
      |_ -> acc)
    t
    M.empty

        
  
    (*
arse後にやるべきこと
valuevarの区別。
applicationとrefinment dataのapplicationの区別
変数のsortの決定:done
  *)
