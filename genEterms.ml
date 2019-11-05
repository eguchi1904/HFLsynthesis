module Seq = Base.Sequence
type upProp = [`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list] (* \exists.x.\phi(x,r) *)


(* for debug: specify the position of e-term *)

module Context:sig
  type t

  val empty: t

  val push_arg: Program.e -> t -> t

  val push_head: Id.t -> t -> t

  val to_string: t -> string

end = struct

  type t = (Id.t * Program.e list) list

  let empty = []
            
  let push_arg e = function
    |(head, args)::other ->
      (head, e::args)::other
    |[] -> assert false

  let push_head head t =
    (head, [])::t

  let to_string_elm (head, rev_args) = 
    let args_str =
      List.fold_left
        (fun acc e ->
          (Program.to_string_e e)^" "^acc)
        "??"        
        rev_args
    in
    (Id.to_string_readable head)^" "^args_str


  let to_string t =
    if t = [] then  "??"
    else
      List.fold_left
        (fun acc elm ->
          (to_string_elm elm)^"\n> "^acc)
        ""
        t
end

module Log:sig
  val log_trial: Context.t -> AbductionCandidate.t -> PathEnv.t ->  Id.t -> Constraint.t -> unit

  val log_trial_result: bool -> unit
end = struct
  let log_cha = open_out "eterm_search.log"
  let log_trial ctx abduction_candi path_env  var cons  =
    Printf.fprintf
      log_cha
      "TRIAL:\n %s \n?? <- %s\nabduction candidate:\n%s\n pathenv:\n\n%s \nconstraint:\n%s\n\n.......\n"
      (Context.to_string ctx)
      (Id.to_string_readable var)
      (AbductionCandidate.to_string abduction_candi)
      (PathEnv.to_string path_env)
      (Constraint.to_string cons)

  let log_trial_result valid =
    if valid then
      Printf.fprintf
        log_cha
        "\nTRIAL SUCSESS!\n\n\n"
    else
      Printf.fprintf
        log_cha
        "\n\nTRIAL fail\n\n\n"      
end  

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
let split_arg_spec_return_prop ep penv head spec =
  (* extract_fun_specが、argの変数名のfreshnessを保証 *)
  match Hfl.Equations.extract_fun_spec ep head with
  |Some head_spec ->
    (* ここをabduction的な形で綺麗にまとめれば良いな。それだけか。まあ今綺麗にせんでも良いか。 *)
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
    Some (arg_spec, head_spec.retSpec)
  |None -> None

         
let mk_args_prop (args:(Id.t * (Program.e * upProp)) list) sorts =
  (*  bindは真面目に計算すると↓だが、alternationないなら保持しておく必要ない *)
  
  (* let old_binds = *)
  (*   List.map *)
  (*     (fun (_, (_, `Exists (binds, _))) -> binds) *)
  (*     args *)
  (*   |> List.concat *)
  (* in *)
  (* let new_binds = *)
  (*   List.map2 *)
  (*     (fun (x,_) sort -> (x, sort)) *)
  (*     args *)
  (*     sorts *)
  (* in *)
  (* let binds = new_binds@old_binds in *)
  let binds = [] in
  let prop_body =              
    List.map
      (fun (x, (_, `Exists (_, body))) ->
        (* [_v -> x]body *)
        List.map (Hfl.replace Id.valueVar_id x) body)
      args
    |>
      List.concat
  in
  `Exists (binds, prop_body)
  
          
(* ************************************************** *)
(* synthesis main *)
(* ************************************************** *)

            
let gen_vars: Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t
              -> (Id.t * Hfl.baseSort) list -> Hfl.qhorn list
              -> (Program.e * upProp * AbductionCandidate.t) Seq.t = 
  (fun ctx ep penv abduction_candidates scalar_heads spec ->
    let abduction_candidates_sequence =
      Seq.shift_right
        (AbductionCandidate.strengthen abduction_candidates)
        abduction_candidates
    in
    Seq.concat_map
      abduction_candidates_sequence
      ~f:(fun abduction_candidate ->
           Seq.unfold_step
             ~init:scalar_heads (* 変数の候補 *)
             ~f:(function
                 |[]-> Seq.Step.Done
                 |(id, sort)::next_candidates ->
                   let leaf_prop = hfl_prop_of_leaf ep id sort in
                   let abduction_condition =
                     AbductionCandidate.get abduction_candidate
                   in
                   let penv' = PathEnv.add_condition_list
                                 (List.map (fun e -> `Base e) abduction_condition)
                                 penv
                   in
                   let cons = Constraint.make ep penv' ~prop:leaf_prop ~spec:spec in
                   let () = Log.log_trial ctx abduction_candidate penv id cons in                   
                   let valid = Constraint.is_valid cons in
                   let () = Log.log_trial_result valid in
                   if  valid then
                     Seq.Step.Yield ((Program.{head = id; args = []},
                                      leaf_prop,
                                      abduction_candidate),
                                     next_candidates)
                   else
                     Seq.Step.Skip(next_candidates)
                )
         )
  )



let rec gen_args: Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> (Id.t * Hfl.sort * Hfl.qhorn list) list
                  -> int
                  -> ((Id.t * (Program.e * upProp)) list * AbductionCandidate.t) Seq.t = 
  (fun ctx ep penv abduction_candidate arg_specs depth ->
    match arg_specs with
    |[] -> Seq.singleton ([], abduction_candidate)
    |(x, sort, spec)::lest_specs ->
      let term_for_x:(Program.e * upProp * AbductionCandidate.t) Seq.t =
        f ctx ep penv abduction_candidate sort spec depth
      in
      Seq.concat_map
        term_for_x
        ~f:(fun (ex, (`Exists (binds, clauses) as ex_prop), abduction_candidate) ->
          let ex_conds =
            List.map (Hfl.replace x Id.valueVar_id) clauses in
          let penv' = PathEnv.add_condition_list ex_conds penv in
          let ctx = Context.push_arg ex ctx in
          gen_args ctx ep penv' abduction_candidate lest_specs depth
          |> Seq.map
               ~f:(fun (args, acc_abduction_candidate) ->
                 (x,(ex, ex_prop))::args, acc_abduction_candidate)
        )
  )
  

and gen_app_term:Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.qhorn list
                 -> int -> (Id.t * Hfl.funcSort)
                 -> (Program.e * upProp * AbductionCandidate.t) Seq.t = 
  (fun ctx ep penv abduction_candidate spec depth (head,`FunS (arg_sorts, ret_sort))  ->
    let ctx = Context.push_head head ctx in
    match split_arg_spec_return_prop ep penv head spec with
    |Some (arg_specs, ret_prop) ->
      assert (List.length arg_specs = List.length arg_sorts);
      let arg_specs_with_sort =
        List.map2
          (fun (x, spec) sort -> (x, sort, spec))
          arg_specs arg_sorts
      in
      (* 引数列の候補 *)
      let arg_seq = gen_args ctx ep penv abduction_candidate arg_specs_with_sort (depth-1) in
      Seq.map
        arg_seq
        ~f:(fun ((args:(Id.t * (Program.e * upProp)) list), abduction_candidate)  ->
          let `Exists (binds, prop) = mk_args_prop args arg_sorts in
          let up_prop = `Exists (binds, ret_prop::prop) in
          let arg_e_terms = List.map (fun (_, (e, _)) -> e) args in
          let e_term = Program.{head = head
                               ;args = arg_e_terms}
          in
          (e_term, up_prop, abduction_candidate))
  |None -> assert false
  )

  
and gen_app_terms ctx ep penv abduction_candidates spec depth (func_heads:(Id.t * Hfl.funcSort) list) =
  List.map (gen_app_term ctx ep penv abduction_candidates spec depth) func_heads
  |> Seq.round_robin            (* とりあえずround-robinで探索 *)

  
and f ctx ep penv abduction_candidate sort spec depth =
  let HeadCandidates.{scalar = scalar_heads; func = func_heads}
    =  PathEnv.find_heads (Hfl.return_sort sort) penv
  in
  let var_seq = gen_vars ctx ep penv abduction_candidate scalar_heads spec in
  if depth <= 0 then
    var_seq
  else
    let app_term_seq = gen_app_terms ctx ep penv abduction_candidate spec depth func_heads in
    Seq.append var_seq app_term_seq

  
    
let f  ep penv abduction_candidate sort spec depth =
  f (Context.empty) ep penv abduction_candidate sort spec depth
