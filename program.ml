type e = {head: Id.t;  args: e list}

type condition = |ETermCond of e
                 |PredCond of BaseLogic.t
                         
type b =
  |PIf of (condition * b * b)
  |PMatch of e * (case list)
  |PE of e
 and case =  {constructor : Id.t ;
              argNames : (Id.t * Hfl.baseSort) list ;
              body : b}

type t =
  |PRecFun of Id.t * ((Id.t * Hfl.sort) list) * b



   
