type t

val empty:t

val mem: Id. t-> t -> bool

val to_string: t -> string
  
val add: Id.t -> Hfl.sort -> t -> t

val find: Id.t -> t -> Hfl.sort

val find_heads: Hfl.baseSort -> t -> HeadCandidates.t
