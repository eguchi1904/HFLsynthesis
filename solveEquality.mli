(* baseLogicの世界で良いのか *)
val f: exists:(Id.t * BaseLogic.sort) list
       -> equality_premise:(BaseLogic.t * BaseLogic.t) list
       -> (BaseLogic.t * BaseLogic.t * BaseLogic.sort) list
       -> BaseLogic.t M.t option
  
