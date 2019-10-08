type e = {head: Id.t;  args: e list}

type b =
  |PIf of (e * b * b)
  |PMatch of e * (case list)
  |PE of e
 and case =  {constructor : Id.t ; argNames : Id.t list ; body : b}

type t =
  |PRecFun of Id.t * (Id.t list) * b



   
