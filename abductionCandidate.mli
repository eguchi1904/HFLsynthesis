  type t

  val get: t -> BaseLogic.t list
    
  (* tを1段階強化したものの候補を返す *)
  val strengthen: t -> t Base.Sequence.t
    
  val initialize: PathEnv.t -> t -> t

     
