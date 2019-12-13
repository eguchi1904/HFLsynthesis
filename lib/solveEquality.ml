module List = Base.List
open BaseLogic


module Group:sig

  type t

  val to_string: t -> string

  val get_id: t -> Id.t

  val mk_empty: unit -> t

  val add: BaseLogic.t -> t -> t

  val union: t -> t -> t

end= struct

  module TermS =
    Set.Make
      (struct
        type t = BaseLogic.t
        let compare = compare
      end)


  module TermListS =
    Set.Make
      (struct
        type t = BaseLogic.t list
        let compare = compare
      end)
    


  (* appTerms \subset terms && constTerms \subset terms  *)
  type t = {id:Id.t;
            terms: TermS.t;
            appTerms: TermListS.t M.t; (* f -> [(x1,x2); (x3,x4) ...] 取り出しやすいように *)
            constTerms: TermS.t}

  let to_string t =
    let term_str =
      TermS.fold
        (fun e acc ->
          (BaseLogic.p2string e)^"; "^acc)
        t.terms
        ""
    in
    let app_terms_str =
      M.fold
        (fun fname arg_set acc ->
          let args_str = 
            TermListS.fold
              (fun es acc ->
                "("^(List.map ~f:BaseLogic.p2string es |> String.concat ";")^");\n"^acc
              )
              arg_set
              ""
          in
          "  "^(Id.to_string_readable fname)^"-->["^args_str^"]\n"^acc)
        t.appTerms
      ""
    in
    let const_term_str =
            TermS.fold
        (fun e acc ->
          (BaseLogic.p2string e)^"; "^acc)
        t.constTerms
        ""
    in
    Printf.sprintf "[%s] {%s} [%s]"  term_str app_terms_str const_term_str
    
  let get_id t = t.id
               

  let mk_empty () = 
    let id = Id.genid "eq_class" in
    {id = id;
     terms = TermS.empty;
     appTerms = M.empty;
     constTerms = TermS.empty
    }


  let add_app_terms fname es m =
    match M.find_opt fname m with
    |Some terms_set -> 
      (M.add fname (TermListS.add es terms_set) m)
    |None -> M.add fname (TermListS.singleton es) m

    
  let add e t=
    match e with
    |UF (_, fname, args) ->
      {id = t.id;
       terms =  TermS.add e t.terms;
       appTerms = add_app_terms fname args t.appTerms;
       constTerms = t.constTerms}
    |Cons (_, _, []) ->
      {id = t.id;
       terms =  TermS.add e t.terms;
       appTerms =  t.appTerms;
       constTerms = TermS.add e t.constTerms}
    |Cons (_, cons, args) ->
      {id = t.id;
       terms =  TermS.add e t.terms;
       appTerms = add_app_terms cons args t.appTerms;
       constTerms = t.constTerms}
    |Int _ |Bool _ ->
      {id = t.id;
       terms = TermS.add e t.terms;
       appTerms =  t.appTerms;
       constTerms = TermS.add e t.constTerms}
    |_ ->
      {id = t.id;
       terms =  TermS.add e t.terms;
       appTerms =  t.appTerms;
       constTerms = t.constTerms}

  let union t1 t2 =
    {id = t1.id;
     terms = TermS.union t1.terms t2.terms;
     appTerms =
       M.union
         (fun _ args_set1 args_set2 -> Some (TermListS.union args_set1 args_set2))
         t1.appTerms
         t2.appTerms;
     constTerms = TermS.union t1.constTerms t2.constTerms
    }


  let get_const t =
    TermS.choose_opt t.constTerms

end    
            
   
module Env:
sig
  type t

  val empty: t
    
  val to_string: t -> string
    
  val add: BaseLogic.t -> BaseLogic.t -> t -> t

  (* (\* 単純に同値類に含まれているかを確認する *\) *)
  (* (\* len x = len y を確かめるためにx=yを検討する、などはしない。 *\) *)

  (* (\* TermIdTable.to_id の結果 *\) *)
  (* (\* val representative: t -> BaseLogic.t -> Id.t *\) *)
    
  val is_same: t -> BaseLogic.t -> BaseLogic.t -> bool

  val is_same_int_term: exists:Id.t list -> t -> BaseLogic.t -> BaseLogic.t -> BaseLogic.t M.t option

  val add_upper_bound: Id.t -> BaseLogic.t -> t -> t

  val add_lower_bound: BaseLogic.t -> Id.t -> t -> t
    
end = struct
  (* len x, Cons x xs などの項にfreshな変数を割り当てる *)
  (* 定数を特別扱いしたい気持ちになるな... *)
  (* 要素が大きいならunionfindとか使うべきだろうけど、unionあまり発生しないのでこれで良いだろう *)
  type t = {equality:Group.t M.t;
            varInstance: BaseLogic.t M.t; (* 今まで分かった変数のinstantiate *)
            upperBound:BaseLogic.t list M.t;
            lowerBound:BaseLogic.t list M.t
           }


  let empty = {equality = M.empty;
               varInstance = M.empty;
               upperBound = M.empty;
               lowerBound = M.empty}


  (* groupにはほんというにそのまま入っている、とする *)
  let find_group_opt e t =
    let e_id = TermIdTable.to_id e in
    M.find_opt e_id t.equality


  let update_var_instance e1 e2 t =
    let var_instance =
      (match e1, e2 with
       |Var (_, x), _ ->
         let e2' = substitution t.varInstance e2 in
         BaseLogic.subst_compose
           (M.singleton x e2')                  
           t.varInstance
       |_, Var (_, x) ->
         let e1' = substitution t.varInstance e1 in
         BaseLogic.subst_compose
           (M.singleton x e1')                  
           t.varInstance
       | _ ->
          t.varInstance
      )
    in
    {equality = t.equality;
     varInstance = var_instance;
     upperBound = t.upperBound;
     lowerBound = t.lowerBound
    }

  let union g1 g2 t =           (* g1に吸収 *)
    let g1_g2 = Group.union g1 g2 in
    let g1_id = Group.get_id g1 in
    let g2_id = Group.get_id g2 in    
    {equality =
       M.map
         (fun group ->
           let group_id = Group.get_id group in
           if group_id = g1_id || group_id = g2_id then
             g1_g2
           else
             group
         )
         t.equality ;
     varInstance = t.varInstance;
     upperBound = t.upperBound;
     lowerBound = t.lowerBound
    }
    
    
  let add e1 e2 t =
    let t = update_var_instance e1 e2 t in
    match (find_group_opt e1 t), (find_group_opt e2 t) with
    |(Some e1_group), (Some e2_group) -> 
      if Group.get_id e1_group = Group.get_id e2_group then t
      else
        union e1_group e2_group t
    |(Some e1_group), None ->
      let e2_group = Group.mk_empty () |> Group.add e2 in
      union e1_group e2_group t
    |None , (Some e2_group) ->
      let e1_group = Group.mk_empty () |> Group.add e1 in
      union e2_group e1_group t
    |None, None ->
      let e1_group = Group.mk_empty () |> Group.add e1 in      
      let e2_group = Group.mk_empty () |> Group.add e2 in
      union e1_group e2_group t
      
    
    
 
  let is_same t e1 e2 =
    match (find_group_opt e1 t), (find_group_opt e2 t) with
    |(Some e1_group), (Some e2_group) ->
      Group.get_id e1_group = Group.get_id e2_group
    |_ -> false


        
  let to_string t =
    let eq_list_str =
      M.fold
        (fun id g acc ->
          let dummy_sort = DataS (Id.genid_const "dummy", []) in
          let id_term = TermIdTable.to_term id dummy_sort
                        |> TermIdTable.unfold
          in
          let g_str = Group.to_string g in
          (p2string id_term)^":"^(g_str)^"\n"^acc)
        t.equality
        ""
    in
    "["^eq_list_str^"]"
        

  (* ************************************************** *)
  (* ************************************************** *)    

  (*  *)
  let is_same_int_term ~exists t e1 e2 =
    let e1 = substitution t.varInstance e1
           |> TermIdTable.replace_uf_to_var
    in
    let e2 = substitution t.varInstance e2
             |> TermIdTable.replace_uf_to_var           
    in
    match Polynomial.of_term e1 with
    |None -> None
    |Some e1_poly -> 
      (match Polynomial.of_term e2 with
       |None -> None
       |Some e2_poly -> 
         (match Polynomial.solve_eq ~exists e1_poly e2_poly with
          |Some sita_poly ->
            let new_sita =
              M.mapi
                (fun id e ->
                  let e' = e |> Polynomial.to_term |> TermIdTable.unfold in
                  if (S.mem id (fv_include_v e')) then
                    invalid_arg "solve_int_term: not yet impl"
                  else
                    e'
                )
                sita_poly
            in
            Some new_sita
          |None -> None
         )
      )


  let add_upper_bound n e1 t =
    let upper_map = M.add_list_map n e1 t.upperBound in
    let t = {equality = t.equality;
             upperBound = upper_map;
             varInstance = t.varInstance;
             lowerBound = t.lowerBound}
    in
    let n_lower_bounds =
      match M.find_opt n t.lowerBound with
      |None -> []
      |Some l -> l
    in
    if List.exists
         n_lower_bounds
         ~f:(fun n_lower ->
           match is_same_int_term ~exists:[] t n_lower e1 with
           |None -> false
           |Some sita -> if M.is_empty sita then true
                         else assert false
         )
    then
      add (Var (IntS, n)) e1 t
    else
      t        
    

  let add_lower_bound e1 n t =
    let lower_map = M.add_list_map n e1 t.lowerBound in
    let t = {equality = t.equality;
             varInstance = t.varInstance;
             upperBound = t.upperBound;
             lowerBound = lower_map}
    in
    let n_upper_bounds =
      match M.find_opt n t.upperBound with
      |None -> []
      |Some l -> l
    in
    if List.exists
         n_upper_bounds
         ~f:(fun n_upper ->
           match is_same_int_term ~exists:[] t n_upper e1 with
           |None -> false
           |Some sita -> if M.is_empty sita then true
                         else assert false
         )
    then
      add (Var (IntS, n)) e1 t
    else
      t
        
     
end



  (* let same_int_term ~exists env e1 e2 = *)
  (*   let e1 = reflect_env_to_term env e1 in *)
  (*   let e2 = reflect_env_to_term env e2 *)
  (*   in *)
  (*   match Polynomial.of_term e1 with *)
  (*   |None -> None *)
  (*   |Some e1_poly ->  *)
  (*     (match Polynomial.of_term e2 with *)
  (*      |None -> None *)
  (*      |Some e2_poly ->  *)
  (*        (match Polynomial.solve_eq ~exists e1_poly e2_poly with *)
  (*         |Some sita_poly -> *)
  (*           let new_sita = *)
  (*             M.mapi *)
  (*               (fun id e -> *)
  (*                 let e' = e |> Polynomial.to_term |> TermIdTable.unfold in *)
  (*                 if (S.mem id (fv_include_v e')) then *)
  (*                   invalid_arg "solve_int_term: not yet impl" *)
  (*                 else *)
  (*                   e' *)
  (*               ) *)
  (*               sita_poly *)
  (*           in *)
  (*           Some new_sita *)
  (*         |None -> None *)
  (*        ) *)
  (*     )   *)




    
(*  
ここを頑張る
　*)
let rec solve acc_sita ~exists env eq_list=
  match eq_list with
  |[] -> Some acc_sita
  |(e1, e2)::other ->
    let e1 = BaseLogic.substitution acc_sita e1 in
    let e2 = BaseLogic.substitution acc_sita e2 in    
    if Env.is_same env e1 e2 then solve acc_sita ~exists env other
    else
    begin
      match (e1, e2) with
      |(Var (_, id), e)         (* \exists i.   (i = e) のパターン *)
           when (List.mem exists id ~equal:(=)
                 && not (S.mem id (fv_include_v e))) ->
        let acc_sita =
          BaseLogic.subst_compose
            (M.singleton id e) acc_sita 
        in
        let exists = List.filter exists ~f:(fun id -> not (M.mem id acc_sita)) in        
        solve acc_sita ~exists env other        
      (* 引数の比較に分解するpattern *)
      |(e, Var (_, id))
           when (List.mem exists id ~equal:(=)
                 && not (S.mem id (fv_include_v e))) ->
        let acc_sita =
          BaseLogic.subst_compose
             (M.singleton id e) acc_sita
        in
        let exists = List.filter exists ~f:(fun id -> not (M.mem id acc_sita)) in        
        solve acc_sita ~exists env other                
      |(Set (_,elms), Set (_,elms'))   ->
        solve acc_sita ~exists env ((List.zip_exn elms elms')@other)
      |(Cons (_, cons, args), Cons (_, cons', args'))  when cons = cons' ->
        solve acc_sita ~exists env ((List.zip_exn args args')@other)
      |(UF (_, head, args), UF (_, head', args'))  when head = head' ->
        solve acc_sita ~exists env ((List.zip_exn args args')@other)
      (* int-termの場合はsyntax以上の比較をしたい *)
      |(Var (IntS, _), _) |(_ , Var (IntS, _))|(Int _, _)|(_, Int _)
      |(Times _, _) |(_, Times _) |(Plus _, _) |(_, Plus _) 
       |(Minus _, _) |(_, Minus _)|(Neg _, _) |(_, Neg _)  ->
        (match Env.solve_int_term  ~exists env e1 e2 with
         |Some new_sita ->
           let acc_sita = BaseLogic.subst_compose
                            new_sita
                            acc_sita
           in
          let exists = List.filter exists ~f:(fun id -> not (M.mem id acc_sita)) in
          solve acc_sita ~exists env other
            
        |None -> None)
       
      | _ -> None
    end
       
          
          
let f ~exists env eq_list =
  solve M.empty ~exists env eq_list
        
        
  
    
        
