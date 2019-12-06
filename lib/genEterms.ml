open Extensions
module Seq = Base.Sequence
type upProp = [`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list] (* \exists.x.\phi(x,r) *)

let iteration_count = ref 0

module Spec:
sig
  type t = {sort:Hfl.sort;
            valid:Hfl.horn list;
            sat:Hfl.clause list option (* deplicate *)
           }

  (* val validity:t -> Hfl.horn list *)

  (* val sort:t -> Hfl.sort *)

end = struct

  type t = {sort:Hfl.sort;
            valid:Hfl.horn list;
            sat:Hfl.clause list option}

  (* let validity t = t.valid *)

  (* let get_sort t = t.sort *)
end

                    
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
          |Program.App {args = [];_} -> 
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




let choose_head_candidates ep penv sort spec =
  let () = ignore (spec, ep) in
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
  
  

let check_consistency_opt penv (`Exists(_, prop)) spec =
  let consistency_spec_opt = spec.Spec.sat in
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



(* existで束縛されている量化子が、引数部分に出現しないこと *)
let exists_variable_occur_check (func_spec:Hfl.Equations.func_spec) =
  let exists = func_spec.exists in
  List.for_all
    (fun (_, clause) ->
      S.for_all
        (fun x -> not (List.mem_assoc x exists))
        (Hfl.fv clause)
    )
    func_spec.argSpecs


(* [(x, \phi(x);....]
   consistency_spec_opt
   からspecを構成する
 *)
let mk_arg_specs:(Id.t * Hfl.sort * Hfl.horn list) list
                 -> Id.t 
                 -> (Id.t * Spec.t) list
  = (fun exists_horns head -> 
    let v' = Id.genid (Id.to_string_readable head) in
    List.map
      (fun (x, sort, horns) ->
        let horns =
          List.map (Hfl.replace_horn Id.valueVar_id v') horns
          |> List.map (Hfl.replace_horn x Id.valueVar_id)
        in
        (x, Spec.{sort = sort; valid =  horns; sat = None}))
      exists_horns
  )
  
 
module SSeq = (val (SortedSequence.generator ~size_max:7)) (* 取り敢えずここで *)
            
(* ************************************************** *)
(* synthesis main *)
(* ************************************************** *)

(* do memo *)
let gen_vars: Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t
              -> (Id.t * Hfl.baseSort) list -> Spec.t
              -> (Program.e * upProp * AbductionCandidate.t) Seq.t = 
  (fun ctx ep penv abduction_candidates scalar_heads spec ->
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
                   let consistence = check_consistency_opt penv leaf_prop spec in
                   if not consistence then Seq.Step.Skip(next_candidates)
                   else
                     let `Exists (_, leaf_prop_body) = leaf_prop in
                     let horns =
                       List.map
                         (fun (`Horn(cs, c)) ->
                           `Horn (leaf_prop_body@cs, c))
                       spec.valid
                     in
                     let cons =
                       Constraint.make
                         ep
                         ~exists:[]                       
                         ~premise:(PathEnv.extract_condition penv')
                         ~horns
                     in
                     let () = Log.log_trial ctx abduction_candidate penv id cons in
                     let valid = Constraint.is_valid cons in
                     let () = Log.log_trial_result valid in
                     if  valid then
                       let var_term = Program.App {head = id; args = []} in
                       Seq.Step.Yield ((var_term,
                                        leaf_prop,
                                        abduction_candidate),
                                       next_candidates)
                     else
                       Seq.Step.Skip(next_candidates)
                )
      )
  )



let rec gen_args: Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> (Id.t * Spec.t ) list
                  -> int
                  -> ((Id.t * (Program.e * upProp)) list * AbductionCandidate.t) SSeq.t = 
  (fun ctx ep penv abduction_candidate arg_specs size_sum ->
    let arg_num = List.length arg_specs in
    if size_sum < arg_num then SSeq.empty 
    else
      match arg_specs with
      |[] -> assert false
      |[(x, x_spec)] ->
        let x_size_max = size_sum - (arg_num -1) in (* >= 1 *)
        let term_for_x:(Program.e * upProp * AbductionCandidate.t) SSeq.t =
          f ctx ep penv abduction_candidate x_spec x_size_max
        in
        SSeq.map
          term_for_x
          ~f:(fun (e_x, prop_x, abduction_candidate) ->
            [(x, (e_x, prop_x))], abduction_candidate)
        ~size_diff:0
      |(x, x_spec)::lest_specs ->
        let x_size_max = size_sum - (arg_num -1) in (* >= 1 *)
        let term_for_x:(Program.e * upProp * AbductionCandidate.t) Seq.t =
          (* ここではseq *)
          f ctx ep penv abduction_candidate x_spec x_size_max |> SSeq.to_seq
        in
        let terms_seq_seq =
          Seq.map
            term_for_x
            ~f:(fun (ex, (`Exists (_, clauses) as ex_prop), abduction_candidate) ->
              let ex_size: int = Program.size_e ex in
              let ex_conds =
                List.map (Hfl.replace Id.valueVar_id x) clauses
              in
              let penv' = PathEnv.add_condition_list ex_conds penv in
              let ctx = Context.push_arg ex ctx in
              gen_args
                ctx ep penv' abduction_candidate lest_specs
                (size_sum - ex_size)
              |> SSeq.map
                   ~f:(fun (args, acc_abduction_candidate) ->
                     (x,(ex, ex_prop))::args, acc_abduction_candidate)
                   ~size_diff:ex_size
            )
        in
        (* terms_seq_seqを結合する *)
        SSeq.concat
          terms_seq_seq
    )

and consist_up_prop_from_args_up_prop
      (head_spec:Hfl.Equations.func_spec) arg_up_prop = 
  let binds = [] in             (* negativeのexistsなので現状サボっている *)
  let args_prop =
    arg_up_prop
    |> 
    List.map
      (fun (x, (`Exists (_, body))) ->
        (* [_v -> x]body *)
        List.map (Hfl.replace Id.valueVar_id x) body)
    |>
      List.concat
  in
  `Exists (binds, head_spec.retSpec::args_prop) 
                                                                  
  
  
(* ここのinstanceには、head_spec.argsでないものも含まれる *)
and consist_app_term_from_exists_var_instances
      head (head_spec:Hfl.Equations.func_spec)
      sita (gen_instances:(Id.t * (Program.e * upProp)) list) abduction_candidate =
  let arg_e_terms_up_prop =
    head_spec.args
    |>
      List.map
        (fun (x, sort) ->
          match M.find_opt x sita with
          |Some e_x ->
            let sort = Hfl.cast2baseSort sort in
            let open BaseLogic in
            let prop =
              `Exists ([], 
                       [`Base (Eq (Var ((Hfl.to_baseLogic_sort sort), Id.valueVar_id),
                                   e_x))]
                      )
            in
            (Program.Formula e_x, (x, prop))
          |None ->
            (match List.assoc_opt x gen_instances with
             |Some (term, prop) -> (term, (x,prop))
             |None -> assert false)
        )
  in
  let arg_e_terms, arg_up_props = List.split arg_e_terms_up_prop in
  let up_prop = consist_up_prop_from_args_up_prop
                  head_spec arg_up_props
  in
  let app_term = Program.App {head = head; args = arg_e_terms} in
  (app_term, up_prop, abduction_candidate)

  
  
and gen_app_term:Context.t -> Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Spec.t
                 -> int -> (Id.t * Hfl.funcSort)
                 -> (Program.e * upProp * AbductionCandidate.t) SSeq.t = 
  (fun ctx ep penv abduction_candidate spec size (head,`FunS (arg_sorts, _))  ->
    let ctx = Context.push_head head ctx in
    let arity = List.length arg_sorts in
    if (arity +1 > size) then SSeq.empty
    else
      (match Hfl.Equations.extract_fun_spec ep head with
       |Some ({fixOp = None; params = [];
              exists = _;       (* negative側のexistsなので、全体でforall *)
              args = args; argSpecs = arg_specs;
              retSpec = ret_spec} as head_spec)->
         if not (exists_variable_occur_check head_spec) then
           invalid_arg "split_arg_spec_return_prop:exists variable occur in arg "
         else
           let spec_horns =
             List.map (fun (`Horn (cs, c)) -> `Horn (ret_spec::cs, c)) spec.valid
           in
           let arg_horn =`Horn ([], List.map snd arg_specs |> Hfl.concat_by_and)
           in
           let solutions_seq =
             Constraint.make
               ep
               ~exists:args
               ~premise:(PathEnv.extract_condition penv)
             ~horns:(arg_horn::spec_horns)
             |> Constraint.solve
           in
           Seq.map
             solutions_seq
             ~f:(fun (sita, exists_horns) ->
               let exists_var_specs =
                 mk_arg_specs exists_horns head
               in
               let exists_var_instances =
                 gen_args ctx ep penv abduction_candidate exists_var_specs (size - 1)
               in
               SSeq.map
                 exists_var_instances
                    ~size_diff:1
                    ~f:(fun (gen_instances, abduction_candidate) ->
                      consist_app_term_from_exists_var_instances
                        head head_spec sita gen_instances abduction_candidate
             ))
           |>
             SSeq.concat
           
       |_ -> assert false
      )
  )
        
        

  
and gen_app_terms ctx ep penv abduction_candidates spec size (func_heads:(Id.t * Hfl.funcSort) list) =
  let sseq_list =
    List.map (gen_app_term ctx ep penv abduction_candidates spec size) func_heads
  in
  List.fold_left
    (fun acc sseq -> SSeq.append acc sseq)
    SSeq.empty
    sseq_list


and f ctx ep penv abduction_candidate spec size =
  let HeadCandidates.{scalar = scalar_heads; func = func_heads}
    =  PathEnv.find_heads (Hfl.return_sort spec.sort) penv
  in
  if size <= 0 then assert false
  else
    let var_seq =
      gen_vars ctx ep penv abduction_candidate scalar_heads spec 
    in    
    if size = 1 then
      SSeq.append_sequence var_seq ~size:1 SSeq.empty
    else
      let app_term_seq =
        gen_app_terms ctx ep penv abduction_candidate spec size func_heads
      in
      SSeq.append_sequence
        var_seq ~size:1 app_term_seq



    
let f ep penv abduction_candidate horns sort max_size =
  let spec = Spec.{sort = sort;valid = horns; sat = None } in
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
      f (Context.empty) ep penv abduction_candidate spec max_size
      |> SSeq.to_seq
    )

