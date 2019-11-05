type t


val empty:t

val to_string: t -> string
  
val get: t -> BaseLogic.t list
  
(* tを1段階強化したものの候補を返す *)
val strengthen: t -> t Base.Sequence.t
  
val initialize: PathEnv.t -> Qualifier.t list -> new_vars:Id.t list -> t -> t


     
