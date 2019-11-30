type t

        
val of_term: BaseLogic.t -> t option

val to_term: t -> BaseLogic.t

val equal: t -> t -> bool
  
val add: t -> t -> t

val solve_eq: exists:Id.t list -> t -> t -> (t M.t) option
 
