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
  
  
(* let rec gen_e ep penv sort spec dmax =  *)
(*   let HeadCandidates.{scalar = scalar_heads; func = func_heads} *)
(*     =  PathEnv.find_heads (Hfl.return_sort sort) penv *)
(*   in *)
(*   Seq.concat_map *)
(*     (Seq.of_list head_candi_list) *)
(*     ~f:(fun (id, sort) -> *)
      
    

