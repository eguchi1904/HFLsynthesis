
module Env:
sig
  type t

  val empty:t

  val to_string: t -> string
    
  val add: BaseLogic.t -> BaseLogic.t -> t -> t

  val add_upper_bound: Id.t -> BaseLogic.t -> t -> t

  val add_lower_bound: BaseLogic.t -> Id.t -> t -> t

  val is_same: t -> BaseLogic.t -> BaseLogic.t -> bool

  val is_same_int_term: exists:Id.t list -> t -> BaseLogic.t -> BaseLogic.t -> BaseLogic.t M.t option

  val decompose_by_app_terms: t -> BaseLogic.t -> BaseLogic.t
                              ->(BaseLogic.t * BaseLogic.t ) list list    
    


  (* 単純に同値類に含まれているかを確認する *)
  (* len x = len y を確かめるためにx=yを検討する、などはしない。 *)
    
  (* val is_same: t -> BaseLogic.t -> BaseLogic.t -> bool *)
    
end
     
(* baseLogicの世界で良いのか *)
val f: exists:Id.t list
       -> Env.t
       -> (BaseLogic.t * BaseLogic.t) list
       -> BaseLogic.t M.t Base.Sequence.t
  
