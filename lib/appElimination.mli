type solution = BaseLogic.t M.t * (Id.t * Hfl.sort) list * (Hfl.horn list)

val expansion_max:int ref
(* かえり値はsitaが反映されたhorn *)
val f:
  BaseLogic.t M.t
 ->exists:(Id.t * Hfl.sort) list 
 ->Hfl.Equations.t 
 ->Hfl.clause list 
 -> Hfl.clause 
 ->solution  Base.Sequence.t


val bind_solutions
    :BaseLogic.t M.t
     -> premise:(Hfl.clause) list  
     -> exists:(Id.t * Hfl.sort) list
     -> 'a list
     -> f:(BaseLogic.t M.t -> 'a -> solution Base.Sequence.t)
     -> solution Base.Sequence.t  

module Log:
sig
  val log_cha: out_channel
    
  val log_solution: string -> solution -> unit
    
end 
  
