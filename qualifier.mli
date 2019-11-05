type t

val to_string: t -> string
  
val make:(Id.t * Hfl.baseSort) list ->  BaseLogic.t -> t

val reveal: t -> (Id.t * Hfl.baseSort) list * BaseLogic.t
   
val gen_formulas: PathEnv.t -> must_include_vars:S.t -> t -> BaseLogic.t list


