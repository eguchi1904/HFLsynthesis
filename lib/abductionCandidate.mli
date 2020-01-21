type t


val empty:t

val add: BaseLogic.t -> t -> t

val add_list: BaseLogic.t list -> t -> t

val to_string: t -> string
  
val get: t -> BaseLogic.t list
  
(* tを1段階強化したものの候補を返す *)
val strengthen: t -> t Base.Sequence.t
  
val initialize: DataType.Env.t -> PathEnv.t -> Qualifier.t list -> new_vars:Id.t list -> t -> t


     
