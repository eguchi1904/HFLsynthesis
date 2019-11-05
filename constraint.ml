open Printf

type t = Hfl.Equations.t * Hfl.clause list * Hfl.qhorn list

let to_string ((_, shared_premise, qhorn_list):t) =
  let shared_premise_str =
    List.map Hfl.clause_to_string shared_premise
    |> String.concat " ;"
  in
  let indent = String.make (4+(String.length shared_premise_str)) ' ' in
  let qhorn_list_str =
    List.map Hfl.qhorn_to_string qhorn_list
    |> String.concat (indent^"\n")
  in
  "["^shared_premise_str^"] * ["^qhorn_list_str^"    \n]"
  
  
       
let rec separate_forall_rec (qhorn:Hfl.qhorn) acc_binds =
  match qhorn with
  | `Forall (x, sort, qhorn') ->
     separate_forall_rec qhorn' ((x, sort)::acc_binds)
  | `Exists _ -> invalid_arg "separate_forall_rec"
  | `Horn (pre, res) -> acc_binds, pre, res

let separate_forall qhorn =
  separate_forall_rec qhorn []
  

       
let make
      (ep:Hfl.Equations.t)
      (penv:PathEnv.t)
      ~prop:(prop:[`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list])
      ~spec:(spec: Hfl.qhorn list)
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
  ep, shared_premise, qhorn_list


let rec clause_to_base (c:Hfl.clause) =
  match c with
  | `Base base_e -> base_e
  | `Or (c1, c2) -> BaseLogic.Or ((clause_to_base c1), (clause_to_base c2))
  | `And (c1, c2) -> BaseLogic.And ((clause_to_base c1), (clause_to_base c2))
  | _ -> assert false
                  
  
let rec clause_to_z3_expr: Hfl.clause -> Z3.Expr.expr =
  (fun c ->
    let base = clause_to_base c  in
    (* let () = Printf.eprintf "clause->z3:%s\n" (BaseLogic.p2string_with_sort base) in *)
    fst (BaseLogic.to_z3_expr base)
  )

let rec is_valid_horn shared_premise (qhorn:Hfl.qhorn) =
  match qhorn with
  | `Horn  (pre_clauses ,res_clause) ->
     let pre_clauses_z3 = List.map clause_to_z3_expr pre_clauses in
     let res_clause_z3 = clause_to_z3_expr res_clause in
     let z3_expr = UseZ3.mk_horn (shared_premise::pre_clauses_z3) res_clause_z3 in
     let valid = UseZ3.is_valid z3_expr in
     (* (Printf.eprintf "\nIS valid\n%s\n\n~~~>%b" (Z3.Expr.to_string z3_expr) valid);      *)
     valid
  | `Forall (_,_, qhorn) -> is_valid_horn shared_premise qhorn
  | `Exists _ -> invalid_arg "is_valid_horn"
     
     
             
(* 適宜拡張していこう。まずは超単純なもののみ *)
let is_valid (ep, shared_premise, qhorn_list) =
  let shared_premise_z3 =
    List.map clause_to_z3_expr shared_premise
    |> UseZ3.bind_and_list
  in
  List.for_all (is_valid_horn shared_premise_z3) qhorn_list
  


let subst map ((ep, shared_premise, qhorn_list):t) :t=
  let shared_premise' = List.map (Hfl.subst map) shared_premise in
  let qhorn_list' =
    List.map
      (Hfl.subst_qhorn map)
      (qhorn_list :> Hfl.qhorn list) in
  (ep, shared_premise', qhorn_list')  
(* \exists arg. cons をsplitするイメーz
中身未実装
 *)

let swap_value_var x v' clause =
  Hfl.replace Id.valueVar_id v' clause
  |> Hfl.replace x Id.valueVar_id

let swap_value_var_qhorn x v' qhorn =
  Hfl.replace_qhorn Id.valueVar_id v' qhorn
  |>  Hfl.replace_qhorn x Id.valueVar_id
  
  
let top:Hfl.clause = Hfl.top `BoolS 
let rec mk_arg_spec (arg:(Id.t * Hfl.sort) list)
                    shared_premise qhorn_list =
  match arg with
  |[] -> invalid_arg "mk_arg_spec"
  |[(id, sort)] ->
    let open BaseLogic in
    [id,List.map
         (Hfl.add_premise_qhorn shared_premise)
         qhorn_list]
  |(id,sort)::lest ->
    (id, [`Horn ([], top)])
    ::(mk_arg_spec lest shared_premise qhorn_list)
    
                

    
let split (arg:(Id.t * Hfl.sort) list) (cons:t) =
  let (ep, shared_premise, qhorn_list) = cons in

  let arg_specs: (Id.t * Hfl.qhorn list) list =
    mk_arg_spec arg shared_premise qhorn_list
  in
  (ep, shared_premise, []), arg_specs

let solve (params:(Id.t * Hfl.abstSort) list) ((ep, shared_premise, qhorn_list):t) =
  match params with
  |[] -> M.empty
  |_::_ -> invalid_arg "not impl yet"



  
  
  
  

       
