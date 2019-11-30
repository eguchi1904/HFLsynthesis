type t = {condition:Hfl.clause list
         ;sortEnv:MlEnv.t
         }          (* 一応Hflと言うことで、 *)

let empty = {condition = []
            ;sortEnv = MlEnv.empty}


let to_string t =
  let cond_str =
    List.map (Hfl.clause_to_string) t.condition
    |> String.concat "; "
  in
  "bindings:"
  ^"\n"^(MlEnv.to_string t.sortEnv)
  ^"\npath conditions:"
  ^"\n"^cond_str
    

    
let add_condition c env =
  {condition = c::env.condition
  ;sortEnv  =env.sortEnv}
 

let add_condition_list cs env =
  {condition = cs@env.condition
  ;sortEnv  =env.sortEnv}
  
let add_bind i sort env =
  {condition = env.condition
  ;sortEnv = MlEnv.add i sort env.sortEnv
  }

let add_bind_list binds env =
  List.fold_right
    (fun (i, sort) acc -> add_bind i sort acc)
    binds
  env
  
                   
let find_heads base env :HeadCandidates.t=
  MlEnv.find_heads base env.sortEnv

let extract_condition env = env.condition
  
  

          
