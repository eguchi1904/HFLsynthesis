module List = Base.List
type t = {
    condition:Hfl.clause list;
    yetExpandApps: [`App of Hfl.application] list; (* sub set of conction *)
    sortEnv:MlEnv.t
         }         

let empty = {yetExpandApps = []
            ;condition = []
            ;sortEnv = MlEnv.empty}


let to_string t =
  let yet_expand_str =
    List.map ~f:(Hfl.clause_to_string) (t.yetExpandApps:> Hfl.clause list)
    |> String.concat "; "
  in
  let cond_str =
    List.map ~f:(Hfl.clause_to_string) t.condition
    |> String.concat "; "
  in
  "bindings:"
  ^"\n"^(MlEnv.to_string t.sortEnv)
  ^"\npath conditions:"
  ^"\n"^"("^yet_expand_str^")"^cond_str
    

    
let add_condition c env =
  match c with
  |`App _ as app_term -> 
    {yetExpandApps = app_term::env.yetExpandApps;
     condition = app_term::env.condition
     ;sortEnv  =env.sortEnv}
  | _ ->
    {yetExpandApps = env.yetExpandApps;
     condition = c::env.condition
     ;sortEnv  =env.sortEnv}     
 

let add_condition_list cs env =
  let app_clauses, other_clauses =
    List.partition_map
      cs
      ~f:(function (`App _ as app_c )-> `Fst app_c | c -> `Snd c)
  in
  {yetExpandApps = app_clauses@env.yetExpandApps
  ;condition = app_clauses@other_clauses@env.condition
  ;sortEnv  =env.sortEnv}
  
let add_bind i sort env =
  {yetExpandApps = env.yetExpandApps;
    condition = env.condition
  ;sortEnv = MlEnv.add i sort env.sortEnv
  }

let add_bind_list binds env =
  List.fold_right
    ~f:(fun (i, sort) acc -> add_bind i sort acc)
    binds
    ~init:env  
  
                   
let find_heads base env :HeadCandidates.t=
  MlEnv.find_heads base env.sortEnv

let extract_condition env = env.condition

open SolveEquality

(* let try_expand ep conditions (`App  {head = head; args = arg_cs;_}) = *)
  
  
  

          
