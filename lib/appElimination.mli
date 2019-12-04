type solution = BaseLogic.t M.t * (Hfl.horn list)
  
val f:
  BaseLogic.t M.t 
  ->exists:(Id.t * Hfl.sort) list 
  ->Hfl.Equations.t 
  ->Hfl.clause list 
  -> Hfl.clause 
  ->solution  Base.Sequence.t

val bind_solutions
     :BaseLogic.t M.t
      -> exists:(Id.t * Hfl.sort) list
      -> 'a list
      -> f:(BaseLogic.t M.t -> 'a -> solution Base.Sequence.t)
      -> solution Base.Sequence.t  
