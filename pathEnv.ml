type t = {condition:Hfl.clause list
         ;sortEnv:MlEnv.t
         }          (* 一応Hflと言うことで、 *)

let empty = {condition = []
            ;sortEnv = MlEnv.empty}

          
let add_condition c env =
  {condition = c::env.condition
  ;sortEnv  =env.sortEnv}
 

let add_bind i sort env =
  {condition = env.condition
  ;sortEnv = MlEnv.add i sort env.sortEnv
  }

                   
let find_heads base env :HeadCandidates.t=
  MlEnv.find_heads base env.sortEnv
  

          
