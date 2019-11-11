type upProp = [`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list] (* \exists.x.\phi(x,r) *)

val iteration_count: int ref
  
val f:Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.sort -> Hfl.qhorn list -> int
      -> (Program.e * upProp * AbductionCandidate.t) Base.Sequence.t
