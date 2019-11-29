module Table:
sig
  type t

  val create: unit -> t

  val to_id:t -> BaseLogic.t -> Id.t

  val to_term: t -> Id.t -> BaseLogic.sort ->  BaseLogic.t

  val to_term_subst: t -> BaseLogic.t M.t

  val is_const_id: t -> Id.t -> bool

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
      
        
        
   

end
    

let global = Table.create ()

let to_id e = Table.to_id global e
            
let to_term id sort = Table.to_term global id sort

let is_const_id id = Table.is_const_id global id 

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


  
                    
    
