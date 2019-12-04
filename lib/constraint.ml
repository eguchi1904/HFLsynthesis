open Printf

type t =
  {equations:Hfl.Equations.t;
   exists: (Id.t * Hfl.sort) list;
   sharedPremise: Hfl.clause list;
   qhorns:Hfl.qhorn list
  }
  

let to_string ({sharedPremise = shared_premise; qhorns = qhorn_list;_}:t) =
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
      ~exists ~premise ~qhorns
  : t
  =
  {equations = ep;
   exists = exists;
   sharedPremise = premise;
   qhorns = qhorns}



  
let rec extract_related_var' vars = function
  | c :: lest ->
     let c_fv = Hfl.fv c in
     if S.exists (fun x -> S.mem x vars) c_fv then
       extract_related_var' (S.union vars c_fv) lest
     else
       extract_related_var' vars lest
  |[] -> vars

let rec extract_related_var vars cs  =
  let vars' = extract_related_var' vars cs in
  if S.equal vars vars' then
    vars
  else
    extract_related_var vars' cs

let rec lift_baseLogic_and =function
  | `Base base :: other ->
     let base_list = BaseLogic.list_and base in
     let cs = List.map (fun base -> `Base base) base_list in
     cs@(lift_baseLogic_and other)

  | clause :: other ->
     clause :: (lift_baseLogic_and other)

  | [] -> []
  
  
let extract_necessary_clauses vars cs =
  let cs = lift_baseLogic_and cs in
  let vars = extract_related_var vars cs in
  List.filter (fun c -> (not (S.is_empty (S.inter vars (Hfl.fv c))))) cs
     
  
let rec is_valid_horn shared_premise (qhorn:Hfl.qhorn) =
  match qhorn with
  | `Horn (_, `Base (BaseLogic.Bool true) ) -> true
  | `Horn  (pre_clauses ,res_clause) ->
     let pre_clauses = shared_premise@pre_clauses in
     (* refine clause: 効果はなかった *)
     (* let related_vars = Hfl.fv res_clause in *)
     (* let pre_clauses = extract_necessary_clauses related_vars pre_clauses in *)

     let pre_clauses_z3 = List.map UseZ3.clause_to_z3_expr pre_clauses |> List.map fst in
     let res_clause_z3,_ = UseZ3.clause_to_z3_expr res_clause in
     let z3_expr = UseZ3.mk_horn pre_clauses_z3 res_clause_z3 in
     let valid = UseZ3.is_valid z3_expr in
     (* (Printf.eprintf "\nIS valid\n%s\n\n~~~>%b" (Z3.Expr.to_string z3_expr) valid); *)

     valid
  | `Forall (_,_, qhorn) ->
     is_valid_horn shared_premise qhorn
  | `Exists _ -> invalid_arg "is_valid_horn"
     
     
             
(* 適宜拡張していこう。まずは超単純なもののみ *)
let is_valid (ep, shared_premise, qhorn_list) =
  List.for_all (is_valid_horn shared_premise) qhorn_list
  


(* let subst map ((ep, shared_premise, qhorn_list):t) :t= *)
(*   let shared_premise' = List.map (Hfl.subst map) shared_premise in *)
(*   let qhorn_list' = *)
(*     List.map *)
(*       (Hfl.subst_qhorn map) *)
(*       (qhorn_list :> Hfl.qhorn list) in *)
(*   (ep, shared_premise', qhorn_list')   *)
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
    (id, [])                    
    ::(mk_arg_spec lest shared_premise qhorn_list)
    
                
    
let split (arg:(Id.t * Hfl.sort) list) (cons:t) =
  let (ep, shared_premise, qhorn_list) = cons in
  let arg_specs: (Id.t * Hfl.qhorn list) list =
    mk_arg_spec arg shared_premise qhorn_list
  in
  (ep, shared_premise, []), arg_specs

let mk_

let solve_horn sita ~exists ep shared_premise (`Horn (premise, result)) =
  AppElimination.f sita ~exists ep (premise@shared_premise) result
  
  
  
let solve {exists = exists; sharedPremise = premise; qhorns = qhorns;equations = ep} =
  let exists_qhorns, horns =
    List.fold_right
      (fun qhorn (acc_exists, acc_horn) ->
        let qhorn_exists, qhorn = Hfl.split_outside_exists qhorn in
        let qhorn_exists:> (Id.t * Hfl.sort) list = qhorn_exists in
        let _, pre, result = separate_forall qhorn in
        (qhorn_exists@acc_exists, (`Horn (pre, result))::acc_horn))
      qhorns
      ([], [])
  in
  let exists_sum = (exists@exists_qhorns) in
  let solutions =
    AppElimination.bind_solutions
      M.empty
      ~exists:exists_sum
      horns
      ~f:(fun sita horn -> solve_horn sita ~exists ep premise horn)
  in
  Base.Sequence.map
    solutions
    ~f:(fun (sita, horns) ->
      let exists_sum = List.filter (fun (x,_) -> not (M.mem x sita)) exists_sum in
      
      (sita, exists_sum, horns)
    )
      
      
      
      
  
  
  
  
  




         
  
  


       
