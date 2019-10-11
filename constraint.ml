

type  forallHorn = [`Horn of Hfl.clause list * Hfl.clause
                   | `Forall of Id.t * Hfl.baseSort * forallHorn]

type t = Hfl.Equations.t * Hfl.clause list * forallHorn list                 
       
let rec separate_forall_rec (qhorn:forallHorn) acc_binds =
  match qhorn with
  | `Forall (x, sort, qhorn') ->
     separate_forall_rec qhorn' ((x, sort)::acc_binds)
  | `Horn (pre, res) -> acc_binds, pre, res

let separate_forall qhorn =
  separate_forall_rec qhorn []
  

       
let make
      (ep:Hfl.Equations.t)
      (penv:PathEnv.t)
      ~prop:(prop:[`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list])
      ~spec:(spec: forallHorn list)
  : t
  =
  let `Exists (_, prop_clauses) = prop in
  let penv_clauses = PathEnv.extract_condition penv in
  let shared_premise = prop_clauses@penv_clauses in
  let qhorn_list =
    List.map
      (fun spec_qhorn ->
        let _, pre, res = separate_forall spec_qhorn in
        `Horn (pre, res))
      spec
  in
  ep, shared_premise, spec


let clause_to_z3_expr: Hfl.clause -> Z3.Expr.expr = function
  | `Base base_e ->  fst (BaseLogic.to_z3_expr base_e)
  | _ -> invalid_arg " not implement yet"
  

let rec is_valid_horn shared_premise (qhorn:forallHorn) =
  match qhorn with
  | `Horn  (pre_clauses ,res_clause) ->
     let pre_clauses_z3 = List.map clause_to_z3_expr pre_clauses in
     let res_clause_z3 = clause_to_z3_expr res_clause in
     let z3_expr = UseZ3.mk_horn (shared_premise::pre_clauses_z3) res_clause_z3 in
     UseZ3.is_valid z3_expr
  | `Forall (_,_, qhorn) -> is_valid_horn shared_premise qhorn
     
     
             
(* 適宜拡張していこう。まずは超単純なもののみ *)
let is_valid (ep, shared_premise, qhorn_list) =
  let shared_premise_z3 =
    List.map clause_to_z3_expr shared_premise
    |> UseZ3.bind_and_list
  in
  List.for_all (is_valid_horn shared_premise_z3) qhorn_list
  
  
  
  
  
  

       
