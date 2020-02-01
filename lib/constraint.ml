open Printf

let case_split = ref false

type t =
  {equations:Hfl.Equations.t;
   exists: (Id.t * Hfl.sort) list;
   sharedPremise: Hfl.clause list;
   horns:Hfl.horn list
  }
  
type conditional =
  |RemainExist  of (Id.t * Hfl.sort * Hfl.horn list) list
  |Abduction of BaseLogic.t list
  |Free               
  

let to_string ({exists = exists; sharedPremise = shared_premise; horns = horn_list;_}:t) =
  let shared_premise_str =
    List.map Hfl.clause_to_string shared_premise
    |> String.concat " ;"
  in
  let indent = String.make (4+(String.length shared_premise_str)) ' ' in
  let qhorn_list_str =
    List.map Hfl.qhorn_to_string (horn_list:> Hfl.qhorn list)
    |> String.concat (indent^"\n")
  in
  let exists_str =
    List.map (fun (x, _) -> Id.to_string_readable x) exists
    |> String.concat "."
  in
  "∃"^exists_str^"["^shared_premise_str^"] *\n   ["^qhorn_list_str^"    \n]"


module Log = struct

  let log_cha = AppElimination.Log.log_cha


  let sita2str sita =
      M.fold
        (fun i e acc ->
          (Id.to_string_readable i)^"-->"
          ^(BaseLogic.p2string e)
          ^"; "
          ^acc)
        sita
        ""    
  let log_appElimination_solution mes (sita, new_exists, horns) =
    let sita_str = sita2str sita in
    let exists_str =
      List.map
        (fun (x, _) -> (Id.to_string_readable x))
        new_exists
      |> String.concat ","
    in
    let horns_str =
      List.map Hfl.qhorn_to_string (horns:> Hfl.qhorn list)
      |> String.concat "\n"
    in
    Printf.fprintf
      log_cha
      "%s\n------------------------------\nsita:%s\n new_exists:%s\nhorns:\n%s"
      mes
       sita_str    
       exists_str
       horns_str
    
    
    

  let log_solution mes (sita, conditional) =
    let sita_str =
      sita2str sita
    in
    match conditional with
    |Free ->
      Printf.fprintf
        log_cha
        "%s\n------------------------------\nsita:%s\n conditinal-free\n"
        mes
        sita_str    
    |Abduction e ->
    Printf.fprintf
      log_cha
      "%s\n------------------------------\nsita:%s\n abduction:\n%s"
      mes
      sita_str    
     (List.map BaseLogic.p2string e |> String.concat ";")
    |RemainExist exists_horns -> 
    let exists_horns_str =
      List.map
        (fun (x, _, horns) ->
          let horns_str =
            List.map
              Hfl.qhorn_to_string
              (horns:> Hfl.qhorn list)
            |>String.concat "\n   "
          in
          (Id.to_string_readable x)^"<::<::<\n "^
            horns_str)
        exists_horns
      |>
        String.concat "\n"
    in
    Printf.fprintf
      log_cha
      "%s\n------------------------------\nsita:%s\n remain exists:\n%s"
    mes
       sita_str    
       exists_horns_str
              

end

       
let rec separate_forall_rec (qhorn:Hfl.qhorn) acc_binds =
  match qhorn with
  | `Forall (x, sort, qhorn') ->
     separate_forall_rec qhorn' ((x, sort)::acc_binds)
  | `Exists _ -> invalid_arg "separate_forall_rec"
  | `Horn (pre, res) -> acc_binds, pre, res

let separate_forall qhorn =
  separate_forall_rec qhorn []


let rec case_split_rec = function
  | (`Or (c1, c2))::other ->
    let splited_other = case_split_rec other in
    (List.map (fun cs -> c1::cs) splited_other)
    @(List.map (fun cs -> c2::cs) splited_other)
  | [] -> [[]]
      
  
let toplevel_case_split  {exists = exists; sharedPremise = premise; horns = horns;equations = ep} =
  if not !case_split  then {exists = exists; sharedPremise = premise; horns = horns;equations = ep}
else
  let premise =
    premise
    |> List.map (fun c -> Hfl.separate_by_and c)
    |>
      List.concat
  in
  let or_clauses, other_clauses =
    Base.List.partition_map
      premise
      ~f:(function | (`Or _ as c) -> `Fst c  | c -> `Snd c)
  in
  let splited_or_caluses = case_split_rec or_clauses in
  let horns: Hfl.horn list =
    List.map
      (fun (`Horn (cs, c)) ->
        List.map
          (fun premise_or_case ->
            let premise_or_case = (premise_or_case:> (Hfl.clause) list) in
            ( `Horn (premise_or_case@cs, c)))
          splited_or_caluses)
      horns
    |>
      List.concat
  in
  {exists = exists; sharedPremise = other_clauses; horns = horns;equations = ep}

       
let make
      (ep:Hfl.Equations.t)
      ~exists ~premise ~horns
  : t
  =
 {equations = ep;
   exists = exists;
   sharedPremise = premise;
   horns = horns}
(* |> toplevel_case_split *)


  
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

  


(* let subst map ((ep, shared_premise, qhorn_list):t) :t= *)
(*   let shared_premise' = List.map (Hfl.subst map) shared_premise in *)
(*   let qhorn_list' = *)
(*     List.map *)
(*       (Hfl.subst_qhorn map) *)
(*       (qhorn_list :> Hfl.qhorn list) in *)
(*   (ep, shared_premise', qhorn_list') *)
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
                   
(* let rec mk_arg_spec (arg:(Id.t * Hfl.sort) list) *)
(*                     shared_premise qhorn_list = *)
(*   match arg with *)
(*   |[] -> invalid_arg "mk_arg_spec" *)
(*   |[(id, sort)] -> *)
(*     let open BaseLogic in *)
(*     [id,List.map *)
(*          (Hfl.add_premise_qhorn shared_premise) *)
(*          qhorn_list] *)
(*   |(id,sort)::lest -> *)
(*     (id, [])                     *)
(*     ::(mk_arg_spec lest shared_premise qhorn_list) *)
    
                
    
(* let split (arg:(Id.t * Hfl.sort) list) (cons:t) = *)
(*   let (ep, shared_premise, qhorn_list) = cons in *)
(*   let arg_specs: (Id.t * Hfl.qhorn list) list = *)
(*     mk_arg_spec arg shared_premise qhorn_list *)
(*   in *)
(*   (ep, shared_premise, []), arg_specs *)

         
  
  
  
  
let distribute_horn_to_exists_var' ~exists horns =
  let exists_horns, remain =
    List.fold_right
      (fun (x, sort) (acc_result, remain_horns) ->
        let horns_with_x, horns_without_x =
          List.partition
            (fun horn -> S.mem x (Hfl.fv_horn horn))
            remain_horns
        in
        ((x, sort, horns_with_x)::acc_result, horns_without_x))
      exists
      ([], horns)
  in
  if
    List.for_all
      (function
       | `Horn (_, `Base (BaseLogic.Bool true)) -> true
       | horn -> UseZ3.horn_to_z3_expr horn
                 |> UseZ3.is_valid
      )
      remain
  then
    Some (RemainExist exists_horns)
  else
    
    let remain_str =
      List.map Hfl.qhorn_to_string (remain:> Hfl.qhorn list)
      |> String.concat "\n"
    in
    let exists_str =
      List.map (fun (x, _) -> Id.to_string_readable x) exists
      |> String.concat "."
    in
    let () = output_string
               Log.log_cha
               ("assert false:\nramain:\n"^remain_str^"\nexists:"^exists_str)
    in
    None
(* assert false *)                (* 起こってほしくない *)
    

let subst_base_term_horn sita =
  fun (`Horn (cs, c)) ->
          `Horn (List.map (Hfl.subst_base_term sita) cs,
                 Hfl.subst_base_term sita c)


(* let impl here *)
let try_abduction ~premise horns =       (* ここで、hornをcheckする *)
  let invalid_horns =
    List.filter
      (fun (`Horn (cs, c)) -> 
        let horn_premise_added =
          `Horn (cs@premise, c)
        in
        if UseZ3.horn_to_z3_expr horn_premise_added
           |> UseZ3.is_valid
        then
          false
        else
          true
      )
      horns
  in
  match
    Base.List.partition_map
      invalid_horns
      ~f:(function
          | `Horn([], `Base e) -> `Fst e
          | horn -> `Snd horn)
  with
  |([], []) -> Some Free
  |(e_list, []) ->
    Some (Abduction e_list)
  |_ -> None
      
        
let mk_condinional ~(premise:Hfl.clause list) sita ~exists horns
    :conditional option =
  (* sitaの反映 *)
  let horns = List.map (subst_base_term_horn sita) horns in
  let exists = List.filter      (* sitaで解決していないもの *)
                 (fun (x,_) -> not (M.mem x sita))
                 exists
  in
  if exists = [] then       
    try_abduction ~premise horns
  else
  let horns =                   (* 出来るだけ別ける *)
    List.map
      (fun (`Horn (cs, c)) ->
            List.map
              (fun c' -> (`Horn (cs, c')))
              (Hfl.separate_by_and c)
      )
      horns
    |> List.concat
  in
  distribute_horn_to_exists_var' ~exists horns
  
      
      
let solve_horn sita ~exists ep shared_premise (`Horn (premise, result)) =
  AppElimination.f sita ~exists ep (premise@shared_premise) result
  |> Base.Sequence.map
       ~f:(fun (sita, new_exists, horns) ->
         let horns =
           List.map
             (fun (`Horn (cs, c)) -> `Horn (premise@cs, c))
             horns
         in
         (sita, new_exists, horns))


              
let solve ~start_message {exists = exists; sharedPremise = premise; horns = horns;equations = ep} =
  (* let exists_qhorns, horns = *)
  (*   List.fold_right *)
  (*     (fun qhorn (acc_exists, acc_horn) -> *)
  (*       let qhorn_exists, qhorn = Hfl.split_outside_exists qhorn in *)
  (*       let qhorn_exists:> (Id.t * Hfl.sort) list = qhorn_exists in *)
  (*       let _, pre, result = separate_forall qhorn in *)
  (*       (qhorn_exists@acc_exists, (`Horn (pre, result))::acc_horn)) *)
  (*     qhorns *)
  (*     ([], []) *)
  (* in *)

  (* これは、何
帰ってくる、hornsにはshared_premiseがないもが入っているOK?
 *)
  let solutions =
    AppElimination.bind_solutions
      M.empty
      ~premise
      ~exists
      horns
      ~f:(fun sita horn -> solve_horn sita ~exists ep premise horn)
  in
  let body =
    Base.Sequence.concat_map
      solutions
      ~f:(fun (sita, new_exists, horns) ->
        (* hornsに出現するもののみをのこす *)
        let new_exists =
          new_exists
        |>List.filter
            (fun (x,_) -> not (M.mem x sita))
          |>List.filter
              (fun (x,_) -> List.exists (fun horn -> S.mem x (Hfl.fv_horn horn)) horns)
        in
        let () =
          Log.log_appElimination_solution
              "\nFOUND app elmination solution:\n"            
              (sita, new_exists, horns)
          in
        let exists_sum =
          List.filter
            (fun (x,_) -> not (M.mem x sita))
            (new_exists@exists)
        in
        match mk_condinional
                ~premise sita ~exists:exists_sum horns
        with
        |None ->  Base.Sequence.empty (* assert false *)
        |Some conditional ->        
          Base.Sequence.singleton (sita, conditional)
      )
  in
  (* sequenceから、要素を取り出そうとするたびにlogを取るように改変↓
     for debug
   *)
  Base.Sequence.unfold_step
    ~init:(1, body)
    ~f:(fun (i, body) ->
      if i mod 2 = 1 then
          let () = Printf.fprintf
                     AppElimination.Log.log_cha
                     "\nTRY TO GET %d'th solution of...\n %s"
                     ((i+1)/2)
                     start_message
          in
          Base.Sequence.Step.Skip (i+1, body)
      else
        match Base.Sequence.next body with
        |None ->
          let () = Printf.fprintf
                     AppElimination.Log.log_cha
                     "\n SOLUTION NOT FOUND (><)\n"
          in
          Base.Sequence.Step.Done
        |Some (solution, body') ->
          let () =
            Log.log_solution
              "\nFOUND solution:\n"            
              solution
          in
          Base.Sequence.Step.Yield (solution,
                                      (i+1, body'))
    )
  |> Base.Sequence.memoize
  
  
      
      
let is_valid ~start_message t =
  match Base.Sequence.hd (solve ~start_message t) with
  |None -> None
  |Some (_, Free) -> Some Free
  |Some (_, Abduction e) -> Some (Abduction e)              (* 保守的に *)
  |Some (_, RemainExist _ ) -> None
  
  
  
  
  
  




         
  
  


       
