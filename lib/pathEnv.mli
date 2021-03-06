type t

val empty :t

val mem: Id.t -> t -> bool

val to_string: t -> string

val add_condition: Hfl.clause -> t -> t

val add_condition_list: Hfl.clause list -> t -> t

val add_bind: Id.t -> Hfl.sort -> t -> t

val add_bind_list: (Id.t * Hfl.sort) list -> t -> t 

val find_heads: Hfl.baseSort -> t -> HeadCandidates.t

val extract_condition: t -> Hfl.clause list

val expand: int -> Hfl.Equations.t -> t -> t
  
val is_sat:t -> bool
