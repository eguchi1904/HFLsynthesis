type baseSort = [`BoolS | `IntS | `DataS of Id.t | `SetS of baseSort]
type sort = [baseSort | `FunS of (sort list * baseSort)]

type topSort = [ `BoolS | `FunS of (sort list * [`BoolS ]) ] (* formulaのtoplevelの型 *)
type abstSort = [`FunS of sort list * [`BoolS] ]             (* 命名が微妙 *)
type funcSort = [`FunS of sort list * baseSort ]
              
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

(* veryアドホック *)
let rec to_baseLogic_sort:baseSort -> BaseLogic.sort = function
  | `BoolS -> BaseLogic.BoolS
  | `IntS ->  BaseLogic.IntS
  | `DataS i -> BaseLogic.DataS (i, [])
  | `SetS s -> BaseLogic.SetS (to_baseLogic_sort s)


type  clause = (*\psi(x,y): predicate type formula *)
  [ `Base of BaseLogic.t
  | `Abs of ((Id.t * sort) list * clause)(* 1階の場合は使わない *)           
  | `App of application
  (* |Unknown of Id.t * sort  (\* unknown predicate *\) *)
  | `Or of clause * clause
  | `And of clause * clause
  ]
  and application =  {head:Id.t;
                      params:abstClause list;  (*否定が取れるpredicateのみをapplyできる。とする. *)
                      args:clause list}

  and  abstClause = [`Abs of (Id.t * sort) list * clause]
                  


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
  
         
let rec subst' =
  (fun predicate_map base_term_map clause ->
  match clause with
  | `Base base_e -> `Base (BaseLogic.substitution base_term_map base_e)
  | `Abs (args, body) -> `Abs (args, subst' predicate_map base_term_map body)
                                       
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
  |`App {head = head; params = _::_; args = _} when M.mem head predicate_map -> assert false
  |`App {head = head; params = params; args = real_args} ->
    `App {head = head;
         params = params;
         args = List.map (subst' predicate_map base_term_map) real_args} 
    
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
  
       
type qhorn 
  = [ `Horn of clause list * clause 
    | `Exists of Id.t * baseSort * qhorn
    | `Forall of Id.t * baseSort * qhorn
    ]

(* type existsHorn = [`Exists of Id.t * baseSort * existsHorn] *)

let rec replace_qhorn x y (qhorn:qhorn) :qhorn=
  match qhorn with
  | `Horn (cs, c) -> `Horn (List.map (replace x y) cs, replace x y c)
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



type fixOp = Nu | Mu

(* fixpoint equations *)
module Equations:
sig
  type t (* = private (fixOp option * fhorn) option array *)

  val make: unit -> t

  val add: t -> Id.t -> fixOp option -> fhorn -> unit

  val find: t -> Id.t -> (fixOp option * fhorn) option


  type func_spec = {fixOp: fixOp option
                   ;params:(Id.t * abstSort) list 
                   ;args:(Id.t * sort) list
                   ;argSpecs:(Id.t * clause) list
                   ;retSpec: clause}

      
  val extract_fun_spec:t -> Id.t -> func_spec option
                       
    
end
  = struct
  (* ここの検索は多発するのでarrayで *)
  type t = (fixOp option * fhorn) option array

  let make () = Array.make 1000 None

  (* f x1 x2 r = [\phi(x1); \phi(x1,x2)] => \phi(x1, x2, r) という形になっていて欲しいな
     とりあえず暗黙の前提として使ってしまう。
 *)
  let add arr id fix_op_opt horn =
    arr.(Id.to_int id) <- Some (fix_op_opt, horn)
    
  let find arr id =
    arr.(Id.to_int id)

  type func_spec = {fixOp: fixOp option
                   ;params:(Id.t * abstSort) list 
                   ;args:(Id.t * sort) list
                   ;argSpecs:(Id.t * clause) list
                   ;retSpec: clause}
    
  let extract_fun_spec arr id =
    match arr.(Id.to_int id) with
    |None -> None
    |Some (None, {params = params;
                  args = args;
                  body= `Horn (pre, c)})
     ->
      assert ((List.length args) = (List.length pre));
      let arg_specs = List.map2
                        (fun (id,_) clause -> id, clause)
                        args
                        pre
      in
      Some {fixOp = None
           ;params = params
           ;args = args
           ;argSpecs  = arg_specs
           ;retSpec = c}
    |_ -> invalid_arg "hfl.extract_fun_spec: not implement yet"
        
      


    
    
end


type t = Equations.t * fhorn
  
               

                
 
                
