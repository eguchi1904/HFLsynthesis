open Extensions
module Seq = Base.Sequence
type upProp = [`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list] (* \exists.x.\phi(x,r) *)

let iteration_count = ref 0
(* for debug and memorization: specify the position of e-term *)
module Context:sig
  type t

  val empty: t

  val push_arg: Program.e -> t -> t

  val push_head: Id.t -> t -> t

  val to_string: t -> string

end = struct

  type t = (Id.t * Program.e list) list
        
  let empty = []
            
  let push_arg e t =
    match t with
    |(head, args)::other ->
      (head, e::args)::other
    |[] -> assert false

  let push_head head t =
    (head, [])::t

  let to_string_elm (head, rev_args) = 
    let args_str =
      List.fold_left
        (fun acc e ->
          (match e with
          |Program.{args = [];_} -> 
            (Program.to_string_e e)^" "^acc
          |_ ->
            "("^(Program.to_string_e e)^") "^acc))
        ""        
        rev_args
    in
    (Id.to_string_readable head)^" "^args_str


  let to_string t =
    let pos = (if t = [] then  "??"
               else
                 List.fold_left
                   (fun acc elm ->
                     if acc = "" then (to_string_elm elm)^"??"
                     else
                       (to_string_elm elm)^"("^acc^")")
                   ""
                   t)
    in
    ">>:"^pos^"\n"
end

module Log:sig
  val log_trial: Context.t -> AbductionCandidate.t -> PathEnv.t ->  Id.t -> Constraint.t -> unit

  val log_trial_result: bool -> unit

  val log_abduction: AbductionCandidate.t -> unit
end = struct

  
  let log_cha = open_out "eterm_search.log"
  let log_trial ctx abduction_candi path_env  var cons  =
    (incr iteration_count);
    Printf.fprintf
      log_cha
      "TRIAL:%d\n %s \n?? <- %s\nabduction condition:\n%s\n pathenv:\n\n%s \nconstraint:\n%s\n\n.......\n@."
      (!iteration_count)
      (Context.to_string ctx)
      (Id.to_string_readable var)
      (AbductionCandidate.get abduction_candi
       |> List.map BaseLogic.p2string |> String.concat ";")
      (PathEnv.to_string path_env)
      (Constraint.to_string cons)

  let log_trial_result valid =
    if valid then
      Printf.fprintf
        log_cha
        "\nTRIAL SUCSESS!\n\n\n@."
    else
      Printf.fprintf
        log_cha
        "\n\nTRIAL fail\n\n\n@."

  let log_abduction abduction_candi =
    Printf.fprintf
      log_cha
      "\n\n--------------------------------------------------\nnext abduction:\n%s\n\n--------------------------------------------------\n\n\n"
    (AbductionCandidate.to_string abduction_candi)
end  


module Memo:sig
  type t

  val make: unit -> t
     
  val add: Context.t -> int -> (Program.e * upProp * AbductionCandidate.t) -> t -> unit

  val touch: Context.t -> int -> t -> unit

  val find: Context.t -> int -> t -> (Program.e * upProp * AbductionCandidate.t) list option

  val clear: t -> unit

  val remove: Context.t -> int -> t -> unit

  val remove_empty: t -> unit
    
end= struct

  (* (ctx,size) ---> [e1; e2;....] *)
  type t = ((Context.t * int), (Program.e * upProp * AbductionCandidate.t) list) Hashtbl.t

  let make () = (Hashtbl.create 1000 :t)

  let add ctx size e (t:t) =
    match Hashtbl.find_opt t (ctx, size) with
    |Some l -> Hashtbl.add t (ctx, size) (l@[e])
    |None -> Hashtbl.add t (ctx, size) [e]


  let touch ctx size t = Hashtbl.add t (ctx, size) []
                       
  let find ctx size t =
    Hashtbl.find_opt t (ctx, size)
           
  let clear t = Hashtbl.clear t


  let remove ctx size t =
    Hashtbl.remove t (ctx, size)

  let remove_empty t =
    Hashtbl.filter_map_inplace
      (fun key var ->
        if var = [] then None
        else Some var)
    t
end

(* グローバルなmemo *)
let memo = Memo.make ()



let choose_head_candidates ep penv sort spec =
  (* ひとまずこれだけ *)
  PathEnv.find_heads (Hfl.return_sort sort) penv


(* 全てexistに潰す。 必要条件　*)
let rec mk_init_consitency_spec_qhorn (qhorn:Hfl.qhorn) =
  match qhorn with
  | `Horn (cs, c) -> c::cs
  | `Exists (_, _, qhorn) -> mk_init_consitency_spec_qhorn qhorn
  | `Forall (_, _, qhorn) -> mk_init_consitency_spec_qhorn qhorn                        
     
      
let mk_init_consitency_spec (spec:Hfl.qhorn list) =
  List.map (mk_init_consitency_spec_qhorn) spec
|> List.concat
  
  

let check_consistency_opt penv (`Exists(_, prop)) consistency_spec_opt =
  match consistency_spec_opt with
  |None -> true
  |Some consistency_spec -> 
    let cond_list = PathEnv.extract_condition penv in
    let cond_list_z3 = List.map
                         UseZ3.clause_to_z3_expr
                         cond_list
                     |> List.map fst
    in
    let prop_z3 = List.map UseZ3.clause_to_z3_expr prop
                |> List.map fst

    in
    let consistency_spec_z3 = List.map UseZ3.clause_to_z3_expr consistency_spec
                            |> List.map fst
    in
    let z3_expr = UseZ3.bind_and_list (cond_list_z3@prop_z3@consistency_spec_z3) in
    UseZ3.is_satisfiable z3_expr
  
  

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

         
let hfl_prop_of_leaf ep id sort :upProp= (* 毎回計算するの出なくキャッシュした方が良さそう->ボトルネックでないのでOK? *)
  let open BaseLogic in
  let phi =
    `Base (Eq ((Var ((Hfl.to_baseLogic_sort sort), id)),
           (Var ((Hfl.to_baseLogic_sort sort), Id.valueVar_id))))
  in
  match inline_equation_of_leaf ep id with
  |Some c ->  `Exists ([], [c;phi])
  |None ->  `Exists ([], [phi])


(* argのconsitency specを構成する 
   match consistency_spec_opt with
    |Some consistency -> 普通に分割
 　　|None -> 引数が2子以上の時のみ、末尾以外の引数にconsistency specを割り当てる
*)
let split_arg_consistency_spec v' head_arg_spec head_ret_spec spec consistency_spec_opt =
  match consistency_spec_opt with
  |Some consistency_spec -> 
    let ret_consistency =
      List.map
        (Hfl.replace Id.valueVar_id v')
        (head_ret_spec::consistency_spec)
    in
    let arg_consistency,_ =
      List.fold_right
        (fun (x, clause) (acc, next_arg_consistency) ->
          (* [x -> v]clause::next_arg_consistency *)
          let x_consistency =
            List.map
              (Hfl.replace x Id.valueVar_id)
              (clause::next_arg_consistency)
          in
          Some (x_consistency)::acc, clause::next_arg_consistency)
        head_arg_spec
        ([], ret_consistency)
    in
    arg_consistency

  |None when List.length head_arg_spec = 1 ->[None]
  |None ->
    assert (List.length head_arg_spec > 1);
    let hd_arg_specs, (z,z_spec) = List.split_tail head_arg_spec in
    let ret_consistency =
      List.map
        (Hfl.replace Id.valueVar_id v')
        (z_spec::head_ret_spec::(mk_init_consitency_spec spec))
    in
    let hd_arg_consistency,_ =
      List.fold_right
        (fun (x, clause) (acc, next_arg_consistency) ->
          (* [x -> v]clause::next_arg_consistency *)
          let x_consistency =
            List.map
              (Hfl.replace x Id.valueVar_id)
              (clause::next_arg_consistency)
          in
          Some (x_consistency)::acc, clause::next_arg_consistency)
        hd_arg_specs
        ([], ret_consistency)
    in
    hd_arg_consistency@[None]

(* 引数のrequireする仕様を構成
   引数の変数名は、freshなものを返す
 *)
let split_arg_spec_return_prop ep penv head spec consistency_spec_opt =
  (* extract_fun_specが、argの変数名のfreshnessを保証 *)
  match Hfl.Equations.extract_fun_spec ep head with
  |Some head_spec ->
    (* ここをabduction的な形で綺麗にまとめれば良いな。それだけか。まあ今綺麗にせんでも良いか。 *)
    let cons = Constraint.make ep penv
                               ~prop:(`Exists ([], [head_spec.retSpec]))
                               ~spec:spec
    in
    let free_cons, splited_arg_specs = (* abduction的なことをする *)
      Constraint.split head_spec.args cons
    in
    (* pramsのpredicateを具体化して、代入する *)
    let p_map =
      (Constraint.solve head_spec.params free_cons:> Hfl.clause M.t)
    in
    (* pmap_を適用 *)
    let splited_arg_specs =
      List.map
        (fun (id, qhorn_list)->
          (id, (List.map (Hfl.subst_qhorn
                            p_map
                         )
                         qhorn_list)
          ))
        splited_arg_specs
    in
    let head_arg_spec =
      List.map
        (fun (id, clause) -> (id, Hfl.subst p_map clause))
        head_spec.argSpecs
    in
    let head_ret_spec = Hfl.subst p_map head_spec.retSpec in
    
    (* caliculate arg spec *)
    let v' = Id.genid (Id.to_string_readable head) in 
    let arg_spec =
      List.map2
        (fun (x, clause) (y, splited_spec) ->
          assert(x = y);
          let splited_spec =    (* phi(x,v) -> phi(v, v') *)
            List.map (Hfl.replace_qhorn Id.valueVar_id v') splited_spec
            |> List.map (Hfl.replace_qhorn y Id.valueVar_id)
          in
          match clause with
          | `Base (BaseLogic.Bool true) ->
             (x, splited_spec)
          | _ -> 
             let clause' = Hfl.replace x Id.valueVar_id clause in
             let qhorn:Hfl.qhorn = `Horn ([], clause') in
             (x, qhorn::splited_spec))
        head_arg_spec
        splited_arg_specs
    in
    
    (* caliculate arg consistency spec *)
    let arg_consistency =
      split_arg_consistency_spec v' head_arg_spec head_ret_spec spec consistency_spec_opt
    in
    (assert (List.length arg_spec = List.length arg_consistency));
    let arg_spec_consistency_list =
      List.map2
        (fun (x, qhorn) x_consistency ->(x, qhorn, x_consistency))
        arg_spec
        arg_consistency
    in          
    Some (arg_spec_consistency_list, head_ret_spec) (* pmap代入しないと *)    
    
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

(* do memo *)
let gen_vars: Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t
              -> (Id.t * Hfl.baseSort) list -> Hfl.qhorn list -> Hfl.clause list option
              -> (Program.e * upProp * AbductionCandidate.t) Seq.t = 
  (fun ctx ep penv abduction_candidates scalar_heads spec consistency_spec_opt ->
    let abduction_candidates_sequence =
      (* Seq.shift_right *)
      (*   (AbductionCandidate.strengthen abduction_candidates) *)
      (*   abduction_candidates *)
      Seq.singleton (abduction_candidates)
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
                   let consistence = check_consistency_opt penv leaf_prop consistency_spec_opt in
                   if not consistence then Seq.Step.Skip(next_candidates)
                   else
                     let cons = Constraint.make ep penv' ~prop:leaf_prop ~spec:spec in
                     let () = Log.log_trial ctx abduction_candidate penv id cons in                   
                     let valid = Constraint.is_valid cons in
                     let () = Log.log_trial_result valid in
                     if  valid then
                       let var_term = Program.{head = id; args = []} in
                       let () = Memo.add ctx 1 (var_term, leaf_prop, abduction_candidate) memo in
                       Seq.Step.Yield ((var_term,
                                        leaf_prop,
                                        abduction_candidate),
                                       next_candidates)
                     else
                       Seq.Step.Skip(next_candidates)
                )
      )
  )



let rec gen_args: Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> (Id.t * Hfl.sort * Hfl.qhorn list * Hfl.clause list option) list
                  -> int list
                  -> ((Id.t * (Program.e * upProp)) list * AbductionCandidate.t) Seq.t = 
  (fun ctx ep penv abduction_candidate arg_specs sizes ->
    assert (List.length sizes = List.length arg_specs);
    match arg_specs,sizes with
    |[],[] -> Seq.singleton ([], abduction_candidate)
    |(x, sort, spec, x_consistency_opt)::lest_specs, size::other_size ->
      let term_for_x:(Program.e * upProp * AbductionCandidate.t) Seq.t =
        f ctx ep penv abduction_candidate sort spec x_consistency_opt size
      in
      Seq.concat_map
        term_for_x
        ~f:(fun (ex, (`Exists (binds, clauses) as ex_prop), abduction_candidate) ->
          let ex_conds =
            List.map (Hfl.replace Id.valueVar_id x) clauses in
          let penv' = PathEnv.add_condition_list ex_conds penv in
          let ctx = Context.push_arg ex ctx in
          gen_args ctx ep penv' abduction_candidate lest_specs other_size
          |> Seq.map
               ~f:(fun (args, acc_abduction_candidate) ->
                 (x,(ex, ex_prop))::args, acc_abduction_candidate)
        )
    |_-> assert false
  )
  
  (* do memo *)
and gen_app_term:Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.qhorn list -> Hfl.clause list option
                 -> int -> (Id.t * Hfl.funcSort)
                 -> (Program.e * upProp * AbductionCandidate.t) Seq.t = 
  (fun ctx ep penv abduction_candidate spec consistency_opt size (head,`FunS (arg_sorts, ret_sort))  ->
    let ctx = Context.push_head head ctx in
    let arity = List.length arg_sorts in
    if (arity +1 > size) then Seq.empty
    else
      match split_arg_spec_return_prop ep penv head spec consistency_opt with
      |Some (arg_specs, ret_prop) ->
        assert (List.length arg_specs = List.length arg_sorts);
        let arg_specs_with_sort =
          List.map2
            (fun (x, spec, x_consistency ) sort -> (x, sort, spec, x_consistency))
            arg_specs arg_sorts
        in
        (* 引数sizeの候補 *)
        let arg_sizes = Combination.split (size-1) arity in
        let arg_seq =
          Seq.concat_map
            (Seq.of_list arg_sizes)
            ~f:(fun arg_size ->
                gen_args ctx ep penv abduction_candidate arg_specs_with_sort arg_size
               )
        in
        Seq.map
          arg_seq
          ~f:(fun ((args:(Id.t * (Program.e * upProp)) list), abduction_candidate)  ->
            let `Exists (binds, prop) = mk_args_prop args arg_sorts in
            let up_prop = `Exists (binds, ret_prop::prop) in
            let arg_e_terms = List.map (fun (_, (e, _)) -> e) args in
            let e_term = Program.{head = head
                                 ;args = arg_e_terms}
            in
            let () = Memo.add ctx size (e_term, up_prop, abduction_candidate) memo in
            (e_term, up_prop, abduction_candidate))
      |None -> assert false
  )

  
and gen_app_terms ctx ep penv abduction_candidates spec consistency_opt size (func_heads:(Id.t * Hfl.funcSort) list) =
  List.map (gen_app_term ctx ep penv abduction_candidates spec consistency_opt size) func_heads
  |> Seq.round_robin            (* とりあえずround-robinで探索 *)


(* size固定した状況でのsynthesis *)
and f ctx ep penv abduction_candidate sort spec consistency_spec size =
  match Memo.find ctx size memo with
  |Some e_list -> Seq.of_list e_list
  |None ->
    let () = Memo.touch ctx size memo in
    let HeadCandidates.{scalar = scalar_heads; func = func_heads}
      =  PathEnv.find_heads (Hfl.return_sort sort) penv
    in
    if size <= 0 then assert false
    else if size = 1 then
      let var_seq =
        gen_vars ctx ep penv abduction_candidate scalar_heads spec consistency_spec
      in    
      var_seq
    else
      let app_term_seq =
        gen_app_terms ctx ep penv abduction_candidate spec consistency_spec size func_heads
      in
      app_term_seq


    
let f ep penv abduction_candidate sort spec max_size =
  (* let () = Memo.clear memo in   *)
  let abduction_candidates_sequence =
    Seq.shift_right
      (AbductionCandidate.strengthen abduction_candidate)
      abduction_candidate
  in
  (* for size = 1 to max_size do *)
  (*   Memo.remove Context.empty size memo *)
  (* done; *)
  Seq.concat_map
    abduction_candidates_sequence
    ~f:(fun abduction_candidate ->
      let () = Log.log_abduction abduction_candidate in
      let () = Memo.clear memo in
      Seq.unfold
        ~init:1
        ~f:(fun size ->
          if size > max_size then None
          else
            let seq = f (Context.empty) ep penv abduction_candidate sort spec None size
                      |> Seq.map  ~f:(fun (e, prop, _) -> (e, prop, abduction_candidate))
            in
            Some (seq,
                  size + 1)
        )
      |>
        Seq.concat
    )

