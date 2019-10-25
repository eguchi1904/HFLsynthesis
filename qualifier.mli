type t

val gen_formulas: PathEnv.t -> must_include_vars:S.t -> t -> BaseLogic.t list
