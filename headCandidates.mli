type t =  {scalar:(Id.t * Hfl.baseSort) list
          ;func:(Id.t * Hfl.funcSort) list}

val empty:t

val add: Id.t -> Hfl.sort -> t -> t
