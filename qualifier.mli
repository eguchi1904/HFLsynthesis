type t

val make:(Id.t * Hfl.baseSort) list ->  BaseLogic.t -> t
   
val gen_formulas: PathEnv.t -> must_include_vars:S.t -> t -> BaseLogic.t list
