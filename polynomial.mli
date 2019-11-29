type t

exception Not_Integer_term
        
val of_term: BaseLogic.t -> t 

val to_term: t -> BaseLogic.t

val add: t -> t -> t

val solve_eq: exists:Id.t list -> t -> t -> (t M.t) option
 
