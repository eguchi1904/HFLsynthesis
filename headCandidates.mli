type t =  {scalar:(Id.t * Hfl.sort) list
          ;func:(Id.t * Hfl.sort) list}

val empty:t

val add: Id.t -> Hfl.sort -> t -> t
