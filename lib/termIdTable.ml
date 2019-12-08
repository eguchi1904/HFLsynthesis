module Table:
sig
  type t

  val create: unit -> t

  val to_id:t -> BaseLogic.t -> Id.t

  val to_term: t -> Id.t -> BaseLogic.sort ->  BaseLogic.t

  val to_term_subst: t -> BaseLogic.t M.t

  val is_const_id: t -> Id.t -> bool

  val replace_uf_to_var: t -> BaseLogic.t -> BaseLogic.t 

end = struct

  type t = {termIdHash:(BaseLogic.t, Id.t) Hashtbl.t;
            idTermHash:(Id.t, BaseLogic.t ) Hashtbl.t}
         
  let create () = {termIdHash = Hashtbl.create 100;
                   idTermHash = Hashtbl.create 100}
                

  let add t e id =
    (Hashtbl.add t.termIdHash e id);
    (Hashtbl.add t.idTermHash id e)

  let to_id: t -> BaseLogic.t -> Id.t =
    (fun t e ->
      match e with
      |Var (_,id) -> id
      |e ->
        match Hashtbl.find_opt t.termIdHash e with
            |Some id -> id
            |None ->
              let e_str = BaseLogic.p2string e in
              let id = Id.genid_const e_str in
              (add t e id);
              id
    )

  let to_term t id sort =
    match Hashtbl.find_opt t.idTermHash id with
    |Some e -> e
    | _ -> Var (sort, id)


  let to_term_subst t =
    Hashtbl.fold
      (fun id e acc ->
        M.add id e acc
      )
      t.idTermHash
      M.empty

  let is_const_id t id  =
    let dummy_sort = BaseLogic.IntS in
    match to_term t id dummy_sort  with
    |Int _ |Bool _ -> true
    |_ -> false


  let rec replace_uf_to_var t e =
    let open BaseLogic in
    match e with
    |Int _ |Bool _ |Var _ -> e
    |UF (sort, _,_) -> Var (sort, to_id t e)
    |Set (sort, elms) ->
      Set (sort, List.map (replace_uf_to_var t) elms)
    |Cons (sort, head, args) ->
      Cons (sort, head, List.map (replace_uf_to_var t) args)
    |Times (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Times (t1', t2')
    |Plus (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Plus (t1', t2')
    |Minus (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Minus (t1', t2')
    |Eq (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Eq (t1', t2')
    |Neq (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Neq (t1', t2')
    |Lt (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Lt (t1', t2')
    |Le (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Le (t1', t2')
    |Gt (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Gt (t1', t2')      
    |Ge (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Ge (t1', t2')      
    |And (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      And (t1', t2')      
    |Or (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Or (t1', t2')      
    |Implies (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Implies (t1', t2')      
    |Iff (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Iff (t1', t2')      
    |Union (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Union (t1', t2')
    |Intersect (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Intersect (t1', t2')      
    |Diff (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Diff (t1', t2')      
    |Member (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Member (t1', t2')      
    |Subset (t1, t2) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      Subset (t1', t2')      
    |Neg t1 ->
      let t1' = replace_uf_to_var t t1 in
      Neg t1'
    |Not t1 ->
      let t1' = replace_uf_to_var t t1 in
      Not t1'
    |If (t1, t2, t3) ->
      let t1' = replace_uf_to_var t t1 in
      let t2' = replace_uf_to_var t t2 in
      let t3' = replace_uf_to_var t t3 in
      If (t1', t2', t3')
      
    | _ -> assert false
        
      
        
        
   

end
    

let global = Table.create ()

let to_id e = Table.to_id global e
            
let to_term id sort = Table.to_term global id sort

let is_const_id id = Table.is_const_id global id

let replace_uf_to_var t = Table.replace_uf_to_var global t

let unfold e =
  let sita = Table.to_term_subst global in
  BaseLogic.substitution sita e

let unfold_const e =
  let sita = Table.to_term_subst global
             |> M.filter
                  (fun _ -> function BaseLogic.Int _ |Bool _ -> true
                                      | _ -> false)
  in
  BaseLogic.substitution sita e  


  
                    
    
