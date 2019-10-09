type t =  {scalar:(Id.t * Hfl.sort) list
          ;func:(Id.t * Hfl.sort) list}

let empty = {scalar =[]; func = []}

let add id sort t =
  if Hfl.is_baseSort sort then
    {scalar = (id, sort)::t.scalar
    ;func = t.func}
  else
    {scalar = t.scalar
    ;func = (id, sort)::t.func}
