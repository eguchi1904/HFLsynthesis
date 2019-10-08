type t

val empty:t
  
val add: Id.t -> Hfl.sort -> t -> t

val find: Id.t -> t -> Hfl.sort

val find_heads: Hfl.baseSort -> t -> (Id.t * Hfl.sort) list
