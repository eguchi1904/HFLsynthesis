val to_id:BaseLogic.t -> Id.t

val to_term:Id.t -> BaseLogic.sort -> BaseLogic.t

val unfold: BaseLogic.t -> BaseLogic.t

val is_const_id: Id.t -> bool
  
val unfold_const: BaseLogic.t -> BaseLogic.t  
