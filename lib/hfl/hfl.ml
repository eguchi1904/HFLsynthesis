type baseSort = [`BoolS | `IntS | `DataS of Id.t | `SetS of baseSort]
type sort = [baseSort | `FunS of (sort list * baseSort)]

type topSort = [ `BoolS | `FunS of (sort list * [`BoolS ]) ] (* formulaのtoplevelの型 *)
type abstSort = [`FunS of sort list * [`BoolS] ]             (* 命名が微妙 *)
type funcSort = [`FunS of sort list * baseSort ]

let rec sort2string: sort -> string = function
  | `BoolS -> "bool"
  | `IntS -> "int"
  | `DataS i ->
    Printf.sprintf "%s" (Id.to_string_readable i) 
  | `SetS s -> Printf.sprintf "%s set " (sort2string (s:>sort))
  | `FunS (args, rets) ->
     let arg_str =
       List.map sort2string args
       |> String.concat "->"
     in
     arg_str^"->"^(sort2string (rets:>sort))
              
let return_sort (sort:sort) :baseSort=
  match sort with
  | `FunS (_, rs) -> rs
  | `BoolS -> `BoolS
  | `IntS -> `IntS
  | `DataS i -> `DataS i
  | `SetS b -> `SetS b

let is_baseSort (sort:sort) =
  match sort with
  | `FunS _ -> false
  | _ -> true

let cast2baseSort (sort:sort) =
  match sort with
  | `BoolS | `IntS | `DataS _ | `SetS _ as base_sort -> base_sort
  | _ -> invalid_arg ("cast2baseSort:"^(sort2string sort))
      

let gen_funSort (sort1:sort) (sort2:sort) =
  match sort2 with
    | `BoolS| `IntS |`DataS _ | `SetS _ as base_sort ->
       `FunS ([sort1], base_sort)
    | `FunS (arg_sorts, ret_sort) ->
       `FunS (sort1::arg_sorts, ret_sort)
       
(* veryアドホック *)
let rec to_baseLogic_sort:baseSort -> BaseLogic.sort = function
  | `BoolS -> BaseLogic.BoolS
  | `IntS ->  BaseLogic.IntS
  | `DataS i -> BaseLogic.DataS (i, [])
  | `SetS s -> BaseLogic.SetS (to_baseLogic_sort s)

let rec of_baseLogic_sort: BaseLogic.sort -> baseSort = function
  |BaseLogic.BoolS -> `BoolS
  |BaseLogic.IntS  -> `IntS
  |BaseLogic.DataS (i, sargs) ->
    assert (sargs = []);
    `DataS i
  |BaseLogic.SetS bs ->
    `SetS (of_baseLogic_sort bs)
  |BaseLogic.AnyS  _ |BaseLogic.UnknownS _ -> assert false


type  clause = (*\psi(x,y): predicate type formula *)
  [ `Base of BaseLogic.t
  | `Abs of ((Id.t * sort) list * clause)(* 1階の場合は使わない *)           
  | `App of application
  | `RData of Id.t * abstClause list * clause (* List (\x.x>0) _v みたいな述語。 実装上特別扱い*)
  (* |Unknown of Id.t * sort  (\* unknown predicate *\) *)
  | `Or of clause * clause
  | `And of clause * clause
  ]
  and application =  {head:Id.t;
                      params:abstClause list;  (*否定が取れるpredicateのみをapplyできる。とする. *)
                      args:clause list}

  and  abstClause = [`Abs of (Id.t * sort) list * clause]

let rec size = function
  | `Base _ -> 1
  | `Abs (_, c) -> size c + 2
  | `App {head = _; params = params; args = args} ->
     let param_size =
       List.map size (params:>clause list) |> List.fold_left (+) 0
     in
     let args_size =
       List.map size args |> List.fold_left (+) 0
     in
     1 + param_size + args_size
  | `RData (_, params, arg) ->
     let param_size =
       List.map size (params:>clause list) |> List.fold_left (+) 0
     in
     1 + param_size + (size arg)
  | `Or (c1, c2) | `And (c1, c2) ->
     1 + (size c1) + (size c2)
     
                
  
                  
let rec fv = function
  | `Base base -> BaseLogic.fv_include_v base
  | `Abs (args, body) ->
     List.fold_left
       (fun acc (id, _) ->
         S.remove id acc)
       (fv body)
       args
  | `App {head = head; params = params; args = args} ->
     let params = (params:>clause list )in
     let params_fv =
       List.fold_left S.union S.empty (List.map fv params)
     in
     let args_fv = 
       List.fold_left S.union S.empty (List.map fv args)     
     in
     S.add
       head
       (S.union
          params_fv
          args_fv)

  | `RData (name, params, arg) ->
     let params = (params:>clause list )in
     let params_fv =
       List.fold_left S.union S.empty (List.map fv params)
     in
     let arg_fv = fv arg in
     S.add
       name
       (S.union
          params_fv
          arg_fv)
  | `Or (c1, c2)| `And (c1, c2) ->
     S.union
       (fv c1)
       (fv c2)

let rec app_term_exist: clause -> bool = function
  | `Base _ -> false
  | `App _ | `RData _ ->  true
  | `Abs (_ ,body) -> app_term_exist body
  | `Or (c1, c2) | `And (c1, c2) ->
     (app_term_exist c1) || (app_term_exist c2)




let rec to_string_abs (`Abs (args, body))= 
     let args_str = args
                    |> List.map
                         (fun (id, sort) -> (Id.to_string_readable id)^":"^(sort2string sort))
                    |> String.concat ","
     in
     "fun "^args_str^" ->"^(clause_to_string body)      
    
and clause_to_string = function
  | `Base base -> (BaseLogic.p2string base)
  | `Abs _ as abs -> to_string_abs abs
  | `App {head = head; params = params; args = args} ->
     let params_str = params
                      |> List.map (fun p -> "("^(to_string_abs p)^")")
                      |> String.concat " "
     in
     let args_str =  args
                      |> List.map (fun p -> (clause_to_string p))
                     |> String.concat " "
     in
     String.concat " " [(Id.to_string_readable head); params_str; args_str]

  | `RData (name, params, arg) ->
     let params_str = params
                      |> List.map (fun p -> "("^(to_string_abs p)^")")
                      |> String.concat " "
     in
     let arg_str = clause_to_string arg in
     String.concat " " [(Id.to_string_readable name); params_str; arg_str]     

  | `And (c1, c2) -> (clause_to_string c1)^"&&&"^(clause_to_string c2)
  | `Or (c1, c2) -> (clause_to_string c1)^"|||"^(clause_to_string c2)                   
     
                    
              
let rec separate_by_and clause =
  match clause with
  | `And (c1,c2) ->
     (separate_by_and c1)@(separate_by_and c2)
  | c -> [c]

let rec concat_by_and (cs:clause list) =
  match cs with
  |[] -> `Base (BaseLogic.Bool true)
  |[e] -> e
  |c::cs' -> `And (c, concat_by_and cs')
    

let extend_map_from_args
      (formal_args:(Id.t * sort) list)
      real_args
      (predicate_map: abstClause M.t)
      (base_term_map: BaseLogic.t M.t) =
  let predicate_map', base_term_map' =
    List.fold_left2
      (fun (predicate_map', base_term_map') (id, sort) real_arg  ->
        match real_arg with
        | `Base base_e ->
          assert (is_baseSort sort);
          (predicate_map', M.add id base_e base_term_map')
        | `Abs e ->
          assert (not (is_baseSort sort));
          (M.add id (`Abs e) predicate_map', base_term_map')
        | _ ->
           (M.add id (`Abs ([], real_arg)) predicate_map', base_term_map')
      )
      (predicate_map, base_term_map)
      formal_args
      real_args
  in
  predicate_map', base_term_map'
  

let rec subst_abs': abstClause M.t -> BaseLogic.t M.t -> abstClause -> abstClause = 
  (fun predicate_map base_term_map (`Abs (args, body)) ->
     `Abs (args, subst' predicate_map base_term_map body))

    
and subst' =
  (fun predicate_map base_term_map clause ->
  match clause with
  | `Base base_e -> `Base (BaseLogic.substitution base_term_map base_e)
  | `Abs _ as abs_clause->
     let abs' = subst_abs' predicate_map base_term_map abs_clause in
     (abs':> clause)
  | `App {head = head; params = []; args = real_args} when M.mem head predicate_map ->
    let real_args = List.map (subst' predicate_map base_term_map) real_args in
    (match M.find head predicate_map with
     |`Abs (formal_args, body) ->       (* [args -> arg_cluhauses].body *)
       let predicate_map', base_term_map' =
         extend_map_from_args
           formal_args
           (real_args:>clause list)
           predicate_map
           base_term_map
       in
       subst' predicate_map' base_term_map' body)
  | `App {head = head; params = _::_; args = _} when M.mem head predicate_map ->
     (* 今は、Cons p = ... p
        のp煮た委する代入とかを考えているから。こういうことにはならない。というだけ
      *)
     assert false
  | `App {head = head; params = params; args = real_args} ->
    `App {head = head;
         params = params;
         args = List.map (subst' predicate_map base_term_map) real_args}

  | `RData (rdata, params, arg) ->
     let params' =
       List.map
         (subst_abs' predicate_map base_term_map) params in
     let arg' =  subst' predicate_map base_term_map arg in
     `RData (rdata, params', arg')

  |`Or (c1, c2) -> `Or (subst' predicate_map base_term_map c1,
                        subst' predicate_map base_term_map c2)
                 
  |`And (c1, c2) -> `And (subst' predicate_map base_term_map c1,
                        subst' predicate_map base_term_map c2)
  )


let rec replace_abst x y (`Abs (args, body):abstClause) :abstClause=
  `Abs (args, replace x y body)
  
and replace x y clause=     (* return [x -> y].clause *)
  match clause with
  | `Abs _ as abst_clause-> (replace_abst x y abst_clause :> clause)
  | `Base base_e -> `Base (BaseLogic.replace x y base_e)
  | `App {head = head; params = params; args = real_args} when head = x ->
     `App {head = x;
           params = List.map (replace_abst x y) params;
           args = List.map (replace x y) real_args}
  | `App {head = head; params = params; args = real_args} ->
     `App {head = head;
           params = List.map (replace_abst x y) params;
           args = List.map (replace x y) real_args}
  | `RData (rdata, params, arg) ->
     let params' = List.map (replace_abst x y) params in
     let arg' = replace x y arg in
     `RData (rdata, params', arg')
  | `Or (c1, c2) -> `Or (replace x y c1,
                         replace x y c2)
                 
  | `And (c1, c2) -> `And (replace x y c1,
                           replace x y c2)


let split_subst_map :clause M.t -> abstClause M.t * BaseLogic.t M.t
  =
  (fun map ->
    M.fold
      (fun i clause' (predicate_map, base_term_map) ->
        match clause' with
        | `Base e -> (predicate_map, M.add i e base_term_map)
        | `Abs e -> (M.add i (`Abs e) predicate_map, base_term_map)
        | clause' -> M.add i (`Abs ([],(clause':>clause))) predicate_map, base_term_map)
    map
    (M.empty, M.empty))
  
let subst = 
  (fun map clause ->
    if M.is_empty map then clause
    else
      let (predicate_map:abstClause M.t), (base_term_map:BaseLogic.t M.t) = split_subst_map map
      in
      subst' predicate_map base_term_map clause)

let subst_base_term =
  (fun base_term_map clause ->
    if M.is_empty base_term_map then
      clause
    else
    subst' M.empty base_term_map clause)

let subst_base_term_abs =
  (fun base_term_map abs ->
    if M.is_empty base_term_map then
      abs
    else
      subst_abs' M.empty base_term_map abs)
  
let bottom_predicate = function
  | `FunS (arg_sorts, `BoolS) ->
     let formal_args = List.map (fun sort -> (Id.genid "_", sort)) arg_sorts in
     `Abs (formal_args, `Base (BaseLogic.Bool false))


     
let bottom (sort:topSort) =
  match sort with
  | `BoolS -> `Base (BaseLogic.Bool false)
  | `FunS (arg_sorts, `BoolS) -> bottom_predicate (`FunS (arg_sorts, `BoolS))

let top_predicate = function
  | `FunS (arg_sorts, `BoolS) ->
     let formal_args = List.map (fun sort -> (Id.genid "_", sort)) arg_sorts in
     `Abs (formal_args, `Base (BaseLogic.Bool true))

let top (sort:topSort) =
  match sort with
  | `BoolS -> `Base (BaseLogic.Bool true)
  | `FunS (arg_sorts, `BoolS) -> top_predicate (`FunS (arg_sorts, `BoolS))

         
let subst_bottom = 
  (fun predicates clause ->
    let bottom_list: (Id.t * abstClause) list =
    List.map
      (fun (id, sort) -> id, (bottom_predicate sort))
      predicates
  in
  let bottom_map = M.add_list bottom_list M.empty in
  subst' bottom_map M.empty clause
  )
  

let rec clause_to_base (c:clause) =
  match c with
  | `Base base_e -> base_e
  | `Or (c1, c2) -> BaseLogic.Or ((clause_to_base c1), (clause_to_base c2))
  | `And (c1, c2) -> BaseLogic.And ((clause_to_base c1), (clause_to_base c2))
  | _ -> assert false
                  
  


type horn =  [ `Horn of clause list * clause ]

let fv_horn (`Horn (cs , c)) =
  List.fold_left
    (fun acc c -> S.union acc (fv c))
    (fv c)
    cs
  
  
type qhorn 
  = [ horn
    | `Exists of Id.t * baseSort * qhorn
    | `Forall of Id.t * baseSort * qhorn
    ]



let rec qhorn_to_string (qhorn:qhorn) =
  match qhorn with
  | `Horn (pre_cs, c) ->
     let pre_cs_str = List.map (clause_to_string) pre_cs
                      |> String.concat "; "
     in
     "["^pre_cs_str^"] ==> "^(clause_to_string c)
  | `Exists (x, sort, qhorn) ->
     "∃"^(Id.to_string_readable x)^":"^(sort2string (sort:>sort))^"."^(qhorn_to_string qhorn)
  | `Forall (x, sort, qhorn) ->
     "∀"^(Id.to_string_readable x)^":"^(sort2string (sort:>sort))^"."^(qhorn_to_string qhorn)    

    
let rec split_outside_exists (qhorn:qhorn) =
  match qhorn with
  | `Horn _ | `Forall _ -> ([], qhorn)
  | `Exists (x, x_sort, body) ->
     let (binds, body') =  split_outside_exists body in
     (x, x_sort)::binds, body'

let rec add_outside_exists exists qhorn =
  match exists with
  |[] -> qhorn
  |(x, sort)::exists' ->
    `Exists (x, sort, add_outside_exists exists' qhorn)
  
  

(* type existsHorn = [`Exists of Id.t * baseSort * existsHorn] *)

let replace_horn x y (horn:horn) :horn=
  let `Horn (cs, c) = horn in
  `Horn (List.map (replace x y) cs, replace x y c)

let rec replace_qhorn x y (qhorn:qhorn) :qhorn=
  match qhorn with
  | `Horn _ as horn -> (replace_horn x y horn:> qhorn)
  | `Exists (id, sort, qhorn') -> `Exists (id, sort, replace_qhorn x y qhorn')
  | `Forall (id, sort, qhorn') -> `Forall (id, sort, replace_qhorn x y qhorn')

let swap_var_qhorn x y (qhorn:qhorn) :qhorn=
  replace_qhorn x y qhorn
  |> replace_qhorn y x
  
let rec add_premise_qhorn clauses (qhorn:qhorn) :qhorn=
  match qhorn with
  | `Horn (cs, c) -> `Horn (clauses@cs, c)
  | `Exists (id, sort, qhorn') -> `Exists (id, sort, add_premise_qhorn clauses qhorn')
  | `Forall (id, sort, qhorn') -> `Forall (id, sort, add_premise_qhorn clauses qhorn')
    
(* このような肩はつけられないんか *)
(* type 'a substQhorn = abstClause M.t -> BaseLogic.subst -> 'a -> 'a *)
(* constraint 'a = [<qhorn *)
(*                 ] *)
let rec subst_qhorn' = 
  (fun predicate_map base_term_map qhorn ->
  match qhorn with
  | `Horn (cs, c) ->
     let cs' = List.map (subst' predicate_map base_term_map) cs in
     let c' = subst' predicate_map base_term_map c in
     `Horn (cs', c')
  | `Exists (x, sort, qhorn') ->
     let e:> qhorn = 
     `Exists (x, sort, subst_qhorn' predicate_map base_term_map qhorn')
             in
             e
  | `Forall (x, sort, qhorn') ->
     `Forall (x, sort, subst_qhorn' predicate_map base_term_map qhorn')    
  )
let subst_qhorn map qhorn = 
  if M.is_empty map then qhorn
  else
    let (predicate_map:abstClause M.t),
      (base_term_map:BaseLogic.t M.t) = split_subst_map map
    in                
    subst_qhorn' predicate_map base_term_map (qhorn:>qhorn)
    
type fhorn                      
  = {params:(Id.t * abstSort) list (* predicateパラメータ分,実装上便宜的に分ける *)
    ;args:(Id.t * sort) list
    ;body: qhorn}

let fhorn_to_string {params = params; args = args; body = body } =
  let params_str =
    params
    |> List.map
         (fun (p, sort) -> (Id.to_string_readable p)^"[@param]:"^(sort2string (sort:>sort)))
    |> String.concat " "
  in
  let args_str = 
    args
    |> List.map
         (fun (p, sort) -> (Id.to_string_readable p)^":"^(sort2string (sort:>sort)))
    |> String.concat " "
  in
  "fun "^params_str^" "^args_str^" ->"
  ^"\n        "^(qhorn_to_string body)
    

let replace_fhorn x y {params = params;
                        args = args;
                        body = qhorn} =
  {params = params;
   args = args;
   body = replace_qhorn x y qhorn}
  

let sort_of_fhorn {params = params;
                   args = args;
                   body = _} =
  assert (params = []);
  let arg_sort = List.map snd args in
  if arg_sort = [] then
    `BoolS
  else
  `FunS (arg_sort, `BoolS)
  
(* input:   \x. \y. \phi(x,y) 
   output:  \x'.\y'.\phi(x',y')                   
 *)
let alpha_rename {params = params
                 ;args = args
                 ;body = qhorn}
  =
  let freshed_args, fresh_map = 
    List.fold_right
      (fun (id, sort) (acc_args, acc_map)->
        match sort with
        |(`BoolS | `IntS | `DataS _ | `SetS _ as basesort) ->
          let base_sort = to_baseLogic_sort basesort in
          let id' = Id.genid_from_id id in
          let open BaseLogic in
          let id'_var = Var (base_sort, id') in
          ((id', sort)::acc_args, M.add id id'_var acc_map)
        | _  ->
           let id' = Id.genid_from_id id in
           ((id', sort)::acc_args, acc_map))
      args
      ([], M.empty)
  in
  let freshed_qhorn = subst_qhorn' M.empty fresh_map qhorn in
  {params = params
  ;args = freshed_args
  ;body = freshed_qhorn}
          




type fixOp = Nu | Mu

(* fixpoint equations *)
module Equations:
sig
  type t (* = private (fixOp option * fhorn) option array *)

  val to_string: t -> string

  val make: unit -> t

  val add: t -> Id.t -> fixOp option -> fhorn -> unit

  val find: t -> Id.t -> (fixOp option * fhorn) option

  val find_sort: t -> Id.t -> topSort option


  type func_spec = {fixOp: fixOp option
                   ;params:(Id.t * abstSort) list
                   ;exists:(Id.t * baseSort) list
                   ;args:(Id.t * sort) list
                   ;argSpecs:(Id.t * clause) list
                   ;retSpec: clause}

      
  val extract_fun_spec:t -> Id.t -> func_spec option
                       
    
end
  = struct
  (* ここの検索は多発するのでarrayで *)
  type t = (fixOp option * fhorn) option array

  let make () = Array.make 1000 None

  let to_string t =
    Array.fold_left
      (fun (i,acc) opt->
        match opt with
        |None -> (i+1, acc)
        |Some (_, fhorn) ->
          let id = (Id.to_string_readable (Id.of_int i)) in
          (i+1, acc^"\nlet "^id^" ="^(fhorn_to_string fhorn)))
      (0,"")    
      t

  |> snd
        
        

  (* f x1 x2 r = [\phi(x1); \phi(x1,x2)] => \phi(x1, x2, r) という形になっていて欲しいな
     とりあえず暗黙の前提として使ってしまう。
 *)
  let add arr id fix_op_opt horn =
    arr.(Id.to_int id) <- Some (fix_op_opt, horn)
    
  let find arr id =
    if (Id.to_int id) >= 1000 then None
    else
      arr.(Id.to_int id)

  let find_sort arr id =
    match find arr id with
    |None -> None
    |Some (_, fhorn) -> Some (sort_of_fhorn fhorn)
    
  type func_spec = {fixOp: fixOp option
                   ;params:(Id.t * abstSort) list
                   ;exists:(Id.t * baseSort) list
                   ;args:(Id.t * sort) list
                   ;argSpecs:(Id.t * clause) list
                   ;retSpec: clause}

  let extract_fun_spec arr id =
    match arr.(Id.to_int id) with
    |None -> None
    |Some (Some _, _) ->
      invalid_arg "hfl.extract_fun_spec: not implement yet"
    |Some (None, fhorn) ->
      let {params = params; args = args; body= body} = alpha_rename fhorn in
      (match split_outside_exists body with
       |exists, `Horn (pre, c) -> 
         (* Printf.printf "%s !!\n" (Id.to_string_readable id); *)
         assert ((List.length args) = (List.length pre));
         
         let arg_specs = List.map2
                           (fun (id,_) clause -> id, clause)
                           args
                           pre
         in
         Some {fixOp = None
              ;params = params
              ;exists = exists
              ;args = args
              ;argSpecs  = arg_specs
              ;retSpec = c}
       |_ -> invalid_arg "hfl.extract_fun_spec: not implement yet"
      )

      
      


    
    
end


type t = Equations.t * fhorn
  
               

                
 
                
