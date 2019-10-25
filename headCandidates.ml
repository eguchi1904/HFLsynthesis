type t =  {scalar:(Id.t * Hfl.baseSort) list
          ;func:(Id.t * Hfl.funcSort) list
          }

let empty = {scalar =[]; func = []}

let add id (sort:Hfl.sort) t =
  match sort with
  |`BoolS | `IntS | `DataS _ | `SetS _ as sort'->
    {scalar = (id, sort')::t.scalar
    ;func = t.func}
  |`FunS _ as sort' ->
    {scalar = t.scalar
    ;func = (id, sort')::t.func}
