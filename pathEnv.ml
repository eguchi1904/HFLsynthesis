type t = {condition:Hfl.clause list
         ;sortEnv:MlEnv.t
         }          (* 一応Hflと言うことで、 *)

let empty = {condition = []
            ;sortEnv = MlEnv.empty}

let add_condition env c =
  {condition = c::env.condition
  ;sortEnv  =env.sortEnv}

              
          
