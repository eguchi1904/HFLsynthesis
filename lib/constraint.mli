type t

val to_string:t -> string
val make:
  Hfl.Equations.t 
  -> exists:(Id.t * Hfl.sort) list
  -> premise:Hfl.clause list
  -> horns:Hfl.horn list
  -> t
  
val solve: t ->
(BaseLogic.t M.t * (Id.t * Hfl.sort * Hfl.horn list) list) Base.Sequence.t  


(* val is_valid: t -> bool *)

(* val split: (Id.t * Hfl.sort) list -> t -> t * (Id.t * (Hfl.qhorn list)) list *)

(* 制約を満たす述語割り当てを返す *)



(* val subst: Hfl.clause M.t -> t -> t *)
