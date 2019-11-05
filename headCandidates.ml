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

let to_string {scalar = sclar_list; func = func_list} =
  let sclar_list_str =
    sclar_list
    |> List.map
         (fun (x, bsort) ->
           (Id.to_string_readable x)^":"^(Hfl.sort2string (bsort:>Hfl.sort)))
    |> String.concat "; "
  in
  let func_list_str =
    func_list
    |> List.map
         (fun (x, sort) ->
           (Id.to_string_readable x)^":"^(Hfl.sort2string (sort:>Hfl.sort)))
    |> String.concat "; "
  in
  "{sclar=["^sclar_list_str^"]; func=["^func_list_str^"]}"
    
    
