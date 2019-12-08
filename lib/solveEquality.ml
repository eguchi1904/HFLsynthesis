module List = Base.List
open BaseLogic
   
module Env:
sig
  type t

  val empty: t
    
  val to_string: t -> string

    
  val add: BaseLogic.t -> BaseLogic.t -> t -> t

  (* 単純に同値類に含まれているかを確認する *)
  (* len x = len y を確かめるためにx=yを検討する、などはしない。 *)

  (* TermIdTable.to_id の結果 *)
  val representative: t -> BaseLogic.t -> Id.t
    
  val is_same: t -> BaseLogic.t -> BaseLogic.t -> bool

  val solve_int_term: exists:Id.t list -> t -> BaseLogic.t -> BaseLogic.t -> BaseLogic.t M.t option

  val add_upper_bound: Id.t -> BaseLogic.t -> t -> t

  val add_lower_bound: BaseLogic.t -> Id.t -> t -> t    
    
end = struct
  (* len x, Cons x xs などの項にfreshな変数を割り当てる *)
  (* 定数を特別扱いしたい気持ちになるな... *)
  (* 要素が大きいならunionfindとか使うべきだろうけど、unionあまり発生しないのでこれで良いだろう *)
  type t = {equality:Id.t M.t;
            upperBound:BaseLogic.t list M.t;
            lowerBound:BaseLogic.t list M.t
           }

  let empty = {equality = M.empty;
               upperBound = M.empty;
               lowerBound = M.empty}
        

  let group_id t id =
    match M.find_opt id t.equality with
    |Some id' -> id'
    |None -> id

           
  let union g1 g2 t =           (* g1 = g2 *)
    {equality =
       M.map
         (fun group_id ->
           if group_id = g1 then g2
           else
             group_id
         )
         t.equality    
       |> M.add g1 g2
       |> M.add g2 g2;
     upperBound = t.upperBound;
     lowerBound = t.lowerBound
    }

    
    

  let reflect_env_to_term env e =
    BaseLogic.replace_map env.equality e
    |> TermIdTable.unfold_const    

 
  let term_to_env_id env e =
    let e = reflect_env_to_term env e in
    match e with
    |Var (IntS, _)|Int _ |Times _|Plus _ |Minus _ |Neg _ -> (* int_term *)
      (* 結合順序に夜違い等を吸収する *)
      let uf_free_e = TermIdTable.replace_uf_to_var e in
      (match Polynomial.of_term uf_free_e with
      |None -> assert false     (* 入力によってはありうるけど今は想定してないのでリマインダ *)
      |Some poly ->
        TermIdTable.to_id (Polynomial.to_term poly))
    | _ -> TermIdTable.to_id e
      
      
  let representative t e =
    let e_id = term_to_env_id t e |> group_id t in
    e_id
      
      
    
    
  let add e1 e2 t =
    let e1_group = representative t e1 in
    let e2_group = representative t e2 in
    if e1_group = e2_group then t
    else
      (* constを優先的に代表元にする *)
      let e1_group, e2_group =
        if TermIdTable.is_const_id e1_group then
          e2_group, e1_group
        else
          e1_group, e2_group
      in
      union e1_group e2_group t


             
    

    
  let is_same t e1 e2 =
    let e1_group = TermIdTable.to_id e1 |> group_id t in
    let e2_group = TermIdTable.to_id e2 |> group_id t in
    e1_group = e2_group

      

  let to_string t =
    let eq_list_str =
      M.fold
        (fun id g acc ->
          let dummy_sort = DataS (Id.genid_const "dummy", []) in
          let id_term = TermIdTable.to_term id dummy_sort
                        |> TermIdTable.unfold
          in
          let g_term = TermIdTable.to_term g dummy_sort
                       |> TermIdTable.unfold
          in
          (p2string id_term)^"="^(p2string g_term)^";"^acc)
        t.equality
        ""
    in
    "["^eq_list_str^"]"
        
        



  (* ************************************************** *)
  (* ************************************************** *)    


  let solve_int_term ~exists env e1 e2 =
    let e1 = reflect_env_to_term env e1 in
    let e2 = reflect_env_to_term env e2
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
    let n_lower_bounds =
      match M.find_opt n t.lowerBound with
      |None -> []
      |Some l -> l
    in
    if List.exists
         n_lower_bounds
         ~f:(fun n_lower ->
           match solve_int_term ~exists:[] t n_lower e1 with
           |None -> false
           |Some sita -> if M.is_empty sita then true
                         else assert false
         )
    then
      let e1 = reflect_env_to_term t e1 in
      {equality = t.equality;
       upperBound = upper_map;
       lowerBound = t.lowerBound}
      |> add (Var (IntS, n)) e1
    else
      {equality = t.equality;
       upperBound = upper_map;
       lowerBound = t.lowerBound}      
        
    

  let add_lower_bound e1 n t =
    let lower_map = M.add_list_map n e1 t.lowerBound in
    let n_upper_bounds =
      match M.find_opt n t.upperBound with
      |None -> []
      |Some l -> l
    in
    if List.exists
         n_upper_bounds
         ~f:(fun n_upper ->
           match solve_int_term ~exists:[] t n_upper e1 with
           |None -> false
           |Some sita -> if M.is_empty sita then true
                         else assert false
         )
    then
      let e1 = reflect_env_to_term t e1 in
      {equality = t.equality;
       upperBound = t.upperBound;
       lowerBound = lower_map}
      |> add (Var (IntS, n)) e1
    else
      {equality = t.equality;
       upperBound = t.upperBound;
       lowerBound = lower_map}      
        
     
end


  


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
           let acc_sita = M.union
                            (fun _ -> assert false)
                            acc_sita
                            new_sita
           in
          let exists = List.filter exists ~f:(fun id -> not (M.mem id acc_sita)) in
          solve acc_sita ~exists env other
            
        |None -> None)
       
      | _ -> None
    end
       
          
          
let f ~exists env eq_list =
  solve M.empty ~exists env eq_list
        
        
  
    
        
