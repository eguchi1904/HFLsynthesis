val f: exists:(Id.t * Hfl.sort) list 
       ->Hfl.Equations.t 
       ->PathEnv.t
       -> Hfl.clause 
       ->(BaseLogic.t M.t * Hfl.horn list) option
