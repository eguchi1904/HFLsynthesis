type baseSort = [`BoolS | `IntS | `DataS of Id.t | `SetS of baseSort]
type sort = [baseSort | `FunS of (sort list * baseSort)]

type topSort = [ `BoolS | `FunS of sort list * [`BoolS] ]
type abstSort = [`FunS of sort list * [`BoolS] ]
             
let return_sort (sort:sort) :baseSort=
  match sort with
  | `FunS (_, rs) -> rs
  | `BoolS -> `BoolS
  | `IntS -> `IntS
  | `DataS i -> `DataS i
  | `SetS b -> `SetS b

let is_baseSort (sort:sort) =
  match sort with
  | `FunS _ -> false
  | _ -> true


type  clause = (*\psi(x,y): predicate type formula *)
  [ `Base of BaseLogic.t
  | `Abs of ((Id.t * sort) list * clause)(* 1階の場合は使わない *)           
  | `App of application
  (* |Unknown of Id.t * sort  (\* unknown predicate *\) *)
  | `Or of clause * clause]
  and application =  {head:Id.t;
                      params:abstClause list;  (*否定が取れるpredicateのみをapplyできる。とする. *)
                      args:clause list}

  and  abstClause = [`Abs of (Id.t * sort) list * clause]
                   
let extend_map_from_args
      (formal_args:(Id.t * sort) list)
      (real_args: clause list)
      (predicate_map: abstClause M.t)
      (base_term_map: BaseLogic.t M.t) =
  let predicate_map', base_term_map' =
    List.fold_left2
      (fun (predicate_map', base_term_map') (id, sort) real_arg  ->
        match real_arg with
        | `Base base_e ->
          assert (is_baseSort sort);
          (predicate_map', M.add id base_e base_term_map')
        | `Abs e ->
          assert (not (is_baseSort sort));
          (M.add id (`Abs e) predicate_map', base_term_map')
        | _ ->
           (M.add id (`Abs ([], real_arg)) predicate_map', base_term_map')
      )
      (predicate_map, base_term_map)
      formal_args
      real_args
  in
  predicate_map', base_term_map'

let rec subst' predicate_map base_term_map clause =
  match clause with
  | `Base base_e -> `Base (BaseLogic.substitution base_term_map base_e)
  | `Abs (args, body) -> `Abs (args, subst' predicate_map base_term_map body)
                                       
  | `App {head = head; params = []; args = real_args} when M.mem head predicate_map ->
    let real_args = List.map (subst' predicate_map base_term_map) real_args in
    (match M.find head predicate_map with
     |`Abs (formal_args, body) ->       (* [args -> arg_cluhauses].body *)
       let predicate_map', base_term_map' = extend_map_from_args formal_args real_args predicate_map base_term_map in
       subst' predicate_map' base_term_map' body)
  |`App {head = head; params = _::_; args = _} when M.mem head predicate_map -> assert false
  |`App {head = head; params = params; args = real_args} ->
    `App {head = head;
         params = params;
         args = List.map (subst' predicate_map base_term_map) real_args} 
    
  |`Or (c1, c2) -> `Or (subst' predicate_map base_term_map c1,
                      subst' predicate_map base_term_map c2)
    
let subst map clause =
  let (predicate_map:abstClause M.t), (base_term_map:BaseLogic.t M.t) =
    M.fold
      (fun i clause' (predicate_map, base_term_map) ->
        match clause' with
        | `Base e -> (predicate_map, M.add i e base_term_map)
        | `Abs e -> (M.add i (`Abs e) predicate_map, base_term_map)
        | _ -> M.add i (`Abs ([], clause')) predicate_map, base_term_map)
    map
    (M.empty, M.empty)
  in
  subst' predicate_map base_term_map clause


let bottom_predicate = function
  | `FunS (arg_sorts, `BoolS) ->
     let formal_args = List.map (fun sort -> (Id.genid "_", sort)) arg_sorts in
     `Abs (formal_args, `Base (BaseLogic.Bool false))
     
let bottom (sort:topSort) =
  match sort with
  | `BoolS -> `Base (BaseLogic.Bool false)
  | `FunS (arg_sorts, `BoolS) -> bottom_predicate (`FunS (arg_sorts, `BoolS))


     
let subst_bottom (predicates:(Id.t * abstSort) list) clause =
  let bottom_list: (Id.t * abstClause) list =
    List.map
      (fun (id, sort) -> id, (bottom_predicate sort))
      predicates
  in
  let bottom_map = M.add_list bottom_list M.empty in
  subst' bottom_map M.empty clause
        
  
       
type qhorn 
  = |Horn of clause list * clause
    |Exists of Id.t * baseSort * qhorn
    |Forall of Id.t * baseSort * qhorn

             
type fhorn                      
  = {params:(Id.t * abstSort) list (* predicateパラメータ分,実装上便宜的に分ける *)
    ;args:(Id.t * sort) list
    ;body: qhorn}



type fixOp = Nu | Mu

(* fixpoint equations *)
module Equations:
sig
  type t (* = private (fixOp option * fhorn) option array *)

  val make: unit -> t

  val add: t -> Id.t -> fixOp option -> fhorn -> unit

  val find: t -> Id.t -> (fixOp option * fhorn) option
    
end
  = struct
  (* ここの検索は多発するのでarrayで *)
  type t = (fixOp option * fhorn) option array

  let make () = Array.make 1000 None

  let add arr id fix_op_opt horn =

    arr.(Id.to_int id) <- Some (fix_op_opt, horn)
  let find arr id =
    arr.(Id.to_int id) 
    
end


type t = Equations.t * fhorn
  
               

                
 
                
