type t

val empty :t

val add_condition: Hfl.clause -> t -> t

val add_bind: Id.t -> Hfl.sort -> t -> t

val find_heads: Hfl.baseSort -> t -> HeadCandidates.t

val extract_condition: t -> Hfl.clause list
  
          
