val constraint_count: int ref
  
module type GENETERMS =
  sig
    type upProp = [`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list] (* \exists.x.\phi(x,r) *)


      
    val f:Hfl.Equations.t -> PathEnv.t -> AbductionCandidate.t -> Hfl.sort -> Hfl.qhorn list
          -> (Program.e * upProp * AbductionCandidate.t) Base.Sequence.t
  end

val generator: size_max:int -> (module GENETERMS)
  
