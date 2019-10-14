module Seq = Base.Sequence
type upProp = [`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list] (* \exists.x.\phi(x,r) *)


let choose_head_candidates ep penv sort spec =
  (* ひとまずこれだけ *)
  PathEnv.find_heads (Hfl.return_sort sort) penv


(* ep[id] = \psi(_v)という形になっている者のみに対応 *)
let inline_equation_of_leaf ep id =
  match Hfl.Equations.find ep id with
  |Some (_, {params = _; args = _::_; body = _}) ->
    assert false           (* type error: leaf mustnt have args *)
  |Some (None, {params = params; args = []; body = `Horn ([], c)}) ->
    (* ↓leafでは貪欲にbottomを代入 *)
    let c_bottom = Hfl.subst_bottom params c in
    Some c_bottom
  |Some (_, {params = _; args = []; body = _}) ->
    invalid_arg "not yet implement"
  |None -> None

         
let hfl_prop_of_leaf ep id sort :upProp= (* 毎回計算するの出なくキャッシュした方が良さそう *)
  let open BaseLogic in
  let phi =
    `Base (Eq ((Var ((Hfl.to_baseLogic_sort sort), id)),
           (Var ((Hfl.to_baseLogic_sort sort), Id.valueVar_id))))
  in
  match inline_equation_of_leaf ep id with
  |Some c ->  `Exists ([], [c;phi])
  |None ->  `Exists ([], [phi])

(* 引数のrequireする仕様を構成
   引数の変数名は、freshなものを返す
 *)
let mk_sufficient_arg_spec ep penv head spec = 
  match Hfl.Equations.extract_fun_spec ep head with
  |Some head_spec ->
    let cons = Constraint.make ep penv
                               ~prop:(`Exists ([], [head_spec.retSpec]))
                               ~spec:spec
    in
    let free_cons, splited_arg_specs =
      Constraint.split head_spec.args cons
    in
    (* pramsのpredicateを具体化して、代入する *)
    let p_map =
      Constraint.solve head_spec.params free_cons
    in
    let splited_arg_specs =
      List.map
        (fun (id, qhorn_list)->
          (id, (List.map (Hfl.subst_qhorn
                            (p_map:>Hfl.clause M.t)
                         )
                         qhorn_list)
          ))
        splited_arg_specs
    in
    let arg_spec =
      List.map2
        (fun (x, clause) (y, splited_spec) ->
          assert(x = y);
          let clause' = Hfl.replace x Id.valueVar_id clause in
          let qhorn:Hfl.qhorn = `Horn ([], clause') in
          (x, qhorn::splited_spec))
        head_spec.argSpecs
        splited_arg_specs
    in
    Some arg_spec
  |None -> None
                                     
                                     
  
          
(* ************************************************** *)
(* synthesis main *)
(* ************************************************** *)
          
let gen_leaf ep penv (scalar_heads:(Id.t * Hfl.baseSort) list) spec =
  Seq.unfold_step
    ~init:scalar_heads
    ~f:(function
        |[] -> Seq.Step.Done
        |(id, sort) :: next_candidates-> 
          let leaf_prop = hfl_prop_of_leaf ep id sort in
          let cons = Constraint.make ep penv ~prop:leaf_prop ~spec:spec in
          if Constraint.is_valid cons then
            Seq.Step.Yield ((Program.{head = id; args = []}, leaf_prop),
                            next_candidates)
          else
            Seq.Step.Skip(next_candidates)
       )


let rec gen_args: Hfl.Equations.t -> PathEnv.t -> (Id.t * Hfl.sort * Hfl.qhorn list) list -> (Program.e * upProp) list Seq.t = 
  (fun ep penv arg_specs ->
    match arg_specs with
    |[] -> Seq.singleton []
    |(x, sort, spec)::lest_specs ->
      let term_for_x:(Program.e * upProp) Seq.t =
        gen_e ep penv sort spec
      in
      Seq.concat_map
        term_for_x
        ~f:(fun (ex, (`Exists (binds, clauses) as ex_prop)) ->
          let ex_conds =
            List.map (Hfl.replace x Id.valueVar_id) clauses in
          let penv' = PathEnv.add_condition_list ex_conds penv in
          gen_args ep penv' lest_specs
          |> Seq.map
               ~f:(fun lest_arg_list -> (ex, ex_prop)::lest_arg_list)
        )

                
  
let gen_node ep penv (head,`FunS (arg_sorts, ret_sort)) spec =
  match mk_sufficient_arg_spec ep penv head spec with
  |Some arg_specs ->
    assert (List.length arg_specs = List.length arg_sorts);
    let arg_specs_with_sort =
      List.map2
        (fun (x, spec) sort -> (x, sort, spec))
        arg_specs arg_sorts
    in
    let arg_seq = gen_args ep penv arg_specs_with_sort in

    
    
    
    

                                                              
  
let gen_nodes ep penv (func_heads:(Id.t * Hfl.funcSort) list) spec =
assert false
       
  
(* let rec gen_e ep penv sort spec dmax = *)
(*   let HeadCandidates.{scalar = scalar_heads; func = func_heads} *)
(*     =  PathEnv.find_heads (Hfl.return_sort sort) penv *)
(*   in *)
(*   let leaf_seq = gen_leaf ep penv scalar_heads spec in *)
(*   let node_seq = gen_node ep penv func_heads spec in *)

  
    

