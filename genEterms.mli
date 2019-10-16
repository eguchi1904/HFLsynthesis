type upProp = [`Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list] (* \exists.x.\phi(x,r) *)
            
val f:Hfl.Equations.t -> PathEnv.t -> Hfl.sort -> Hfl.qhorn list
      -> (Program.e * [`Exists of upProp]) Base.Sequence.t
