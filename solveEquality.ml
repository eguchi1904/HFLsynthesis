module List = Base.List
open BaseLogic
   
module Env:
sig
  type t
     
  val add: BaseLogic.t -> BaseLogic.t -> t -> t

  (* 単純に同値類に含まれているかを確認する *)
  (* len x = len y を確かめるためにx=yを検討する、などはしない。 *)

  (* TermIdTable.to_id の結果 *)
  val representative: t -> BaseLogic.t -> Id.t
    
  val is_same: t -> BaseLogic.t -> BaseLogic.t -> bool
    
end = struct
  (* len x, Cons x xs などの項にfreshな変数を割り当てる *)
    
  (* 要素が大きいならunionfindとか使うべきだろうけど、unionあまり発生しないのでこれで良いだろう *)
  type t = (Id.t M.t)  

  let group_id t id =
    match M.find_opt id t with
    |Some id' -> id'
    |None -> id

           
  let union g1 g2 t =           (* g1 = g2 *)
    M.map
      (fun group_id ->
        if group_id = g1 then g2
        else
          group_id
      )
    t

  let add e1 e2 t =
    let e1_group = TermIdTable.to_id e1 |> group_id t in
    let e2_group = TermIdTable.to_id e2 |> group_id t in
    if e1_group = e2_group then t
    else
      union e1_group e2_group t


  let representative t e =
    let e_id = TermIdTable.to_id e |> group_id t in
    e_id
             
    

    
  let is_same t e1 e2 =
    let e1_group = TermIdTable.to_id e1 |> group_id t in
    let e2_group = TermIdTable.to_id e2 |> group_id t in
    e1_group = e2_group
    
end

let rec express_int_term_by_representative_variable env e =
  match e with
  |Int i -> Int i
  |UF (IntS,_, _) |Var (IntS, _)-> Var (IntS, Env.representative env e)
  |Times (t1, t2) ->
    let t1' = express_int_term_by_representative_variable env t1 in
    let t2' = express_int_term_by_representative_variable env t2 in
    Times (t1', t2')
  |Plus (t1, t2) ->
    let t1' = express_int_term_by_representative_variable env t1 in
    let t2' = express_int_term_by_representative_variable env t2 in
    Plus (t1', t2')
  |Minus (t1, t2) ->
    let t1' = express_int_term_by_representative_variable env t1 in
    let t2' = express_int_term_by_representative_variable env t2 in
    Minus (t1', t2')
  |Neg t1 ->
    let t1' = express_int_term_by_representative_variable env t1 in
    Neg t1'
  | _ -> invalid_arg "express_int_term_by_representative_variable: not int term"



let solve_int_term acc_sita ~exists env e1 e2 =
  let e1 = express_int_term_by_representative_variable env e1 in
  let e2 = express_int_term_by_representative_variable env e2 in  
  let e1_poly = Polynomial.of_term e1 in
  let e2_poly = Polynomial.of_term e2 in
  match Polynomial.solve_eq ~exists e1_poly e2_poly with
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
    let acc_sita = M.union
                     (fun _ -> assert false)
                     acc_sita
                     new_sita
    in
    Some acc_sita
  |None -> None
  


let rec solve acc_sita ~exists env eq_list=
  match eq_list with
  |[] -> Some acc_sita
  |(e1, e2)::other ->
    if Env.is_same env e1 e2 then solve acc_sita ~exists env other
    else
    begin
      match (e1, e2) with
      |(Var (_, id), e)
           when (List.mem exists id ~equal:(=)
                 && not (S.mem id (fv_include_v e))) ->
        let acc_sita = M.add id e acc_sita in
        let exists = List.filter exists ~f:(fun id -> not (M.mem id acc_sita)) in        
        solve acc_sita ~exists env other        
      (* 引数の比較に分解するpattern *)
      |(e, Var (_, id))
           when (List.mem exists id ~equal:(=)
                 && not (S.mem id (fv_include_v e))) ->
        let acc_sita = M.add id e acc_sita in
        let exists = List.filter exists ~f:(fun id -> not (M.mem id acc_sita)) in        
        solve acc_sita ~exists env other                
      |(Set (_,elms), Set (_,elms'))   ->
        solve acc_sita ~exists env ((List.zip_exn elms elms')@other)
      |(Cons (_, cons, args), Cons (_, cons', args'))  when cons = cons' ->
        solve acc_sita ~exists env ((List.zip_exn args args')@other)
      |(UF (_, head, args), UF (_, head', args'))  when head = head' ->
        solve acc_sita ~exists env ((List.zip_exn args args')@other)
      (* int-termの場合はsyntax以上の比較をしたい *)
      |(Times _, _) |(_, Times _) |(Plus _, _) |(_, Plus _) 
       |(Minus _, _) |(_, Minus _)|(Neg _, _) |(_, Neg _)  ->
        (match solve_int_term acc_sita ~exists env e1 e2 with
        |Some acc_sita ->
          let exists = List.filter exists ~f:(fun id -> not (M.mem id acc_sita)) in
          solve acc_sita ~exists env other
        |None -> None)
       
      | _ -> None
    end
       
          
          
        
        
        
  
    
        
