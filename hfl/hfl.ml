type baseSort = [`BoolS | `IntS | `DataS of Id.t | `SetS of baseSort]
type sort = [baseSort | `FunS of (sort list * baseSort)]

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
       
type clause = (*\psi(x,y): predicate type formula *)
  |Base of BaseLogic.t
  |Abs of ((Id.t * sort) list * clause)(* 1階の場合は使わない *)           
  |App of Id.t * clause list
  |Unknown of Id.t * sort  (* unknown predicate *)
  |And of clause * clause
  |Or of clause * clause

       
type qhorn 
  = |Horn of clause list * clause
    |Exists of Id.t * baseSort * qhorn
    |Forall of Id.t * baseSort * qhorn

             
type fhorn                      
  = {params:(Id.t * sort) list (* パラメータ分,便宜的に分ける *)
    ;args:(Id.t * sort) list
    ;body: qhorn}



type fixOp = Nu | Mu

(* fixpoint equations *)
module Equations:
sig
  type t (* = private (fixOp option * fhorn) option array *)

  val make: unit -> t

  val add: t -> Id.t -> fixOp option -> fhorn -> unit

  val find: t -> Id.t -> (fixOp option * fhorn)
    
end
  = struct
  (* ここの検索は多発するのでarrayで *)
  type t = (fixOp option * fhorn) option array

  let make () = Array.make 1000 None

  let add arr id fix_op_opt horn =
    arr.(Id.to_int id) <- Some (fix_op_opt, horn)

  let find arr id =
    match arr.(Id.to_int id) with
    |Some s -> s
    |None -> assert false
    
end

  
type t = Equations.t * fhorn
  
               

                
 
                
