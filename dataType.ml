(* ************************************************** *)
(* data型の定義:OCamlでの定義みたいなのと同じ*)
(* ************************************************** *)
type constructor = {name:Id.t;
                    (*　↓引数にidをつけるのはアルゴリズム的には重要でない、match分のcaseでの引数名を決める時に参考にする *)
                    args:(Id.t * Hfl.baseSort) list
                   }
                 
type definition = {name: Id.t
                  ;constructors: constructor list}


(* ************************************************** *)
(* measure: 以下のような形で定義されるもの
   let l = match l with
            |[] -> 0
            |x::xs -> len xs + 1
   
 *)
(* ************************************************** *)
type formulaCase = {constructor: Id.t ; args: (Id.t* Hfl.baseSort) list ; body: BaseLogic.t }

let top_forumulaCase {name = cons;
                      args = args
                     } =
  {constructor = cons;
   args =  args;
   body = BaseLogic.Bool true
  }

  
type measure = {name: Id.t
               ;termination: bool
               ;inputSort: [`DataS of Id.t]
               ;returnSort: Hfl.baseSort
               ;matchCases: formulaCase list}


let add_formulaCase {constructor = cons; args = args1; body = e1}
                    ({constructor = cons'; args = args2; body = e2} as case2)
  =
  if cons <> cons' then invalid_arg "add_formulaCase"
  else
    match e1 with
    |BaseLogic.Bool true -> case2
    | _ ->
       assert (List.length args1 = List.length args2);
       let map = M.add_list2
                   (List.map fst args1)
                   (List.map fst args2)
                   M.empty
       in
       let e1' = BaseLogic.replace_map map e1 in
       {constructor = cons;
        args = args2;
        body = BaseLogic.And (e1', e2)}

  
             
(* ************************************************** *)
(* refineされたsort
 List p v = (v = NIl)
              or(v = x::xs && p x &&  List p xs)
のようなものを表す。
一般にHFLで表現できるので等式環境に入ってるとしても良いが、特別な形で持っておくことにする。とりあえず。
 *)
(* ************************************************** *)             
type refineCase =
  {constructor: Id.t;
   args: (Id.t * Hfl.baseSort * Hfl.clause) list; (* (x, int, x> 0); 等 _vは使わぬ*)
  }


type refine = {name: Id.t
              ;param: (Id.t * Hfl.abstSort) list
              ;constructors: refineCase list
              }


module Env = struct
  type t =
    {constructors: (int, formulaCase) Hashtbl.t; (* constructorのmeasre情報が入っている *)
     datatypes: (int, definition) Hashtbl.t;
     refines: (int, refine) Hashtbl.t;
     dataMeasuresTbl: (int, measure list) Hashtbl.t
    }


  let init () :t=
    {constructors = Hashtbl.create 1024;
     datatypes = Hashtbl.create 1024;
     refines = Hashtbl.create 1024;
     dataMeasuresTbl = Hashtbl.create 1024}

  let fold_datatype (f:Id.t -> definition -> 'a-> 'a) t seed =
    Hashtbl.fold
      (fun i definition acc -> f (Id.of_int i) definition acc)
      t.datatypes
    seed


    
  let add_measure_case
        t
        measure_name
        (`DataS data)
        return_sort
        (case:formulaCase)
    =
    let return_sort = Hfl.to_baseLogic_sort return_sort in
    let e' =
      let open BaseLogic in
      Eq (UF (return_sort,
              measure_name,
              [Var (DataS (data,[]), Id.valueVar_id)]),
          case.body)
    in
    (* constructor用に変換 *)
    let case = {constructor = case.constructor;
                args = case.args;
                body = e'}
    in
    let cons = case.constructor in
    match Hashtbl.find_opt t.constructors (Id.to_int cons) with
    |None -> Hashtbl.add t.constructors (Id.to_int cons)  case
    |Some old_case ->
      let new_case = add_formulaCase old_case case in
      Hashtbl.replace t.constructors  (Id.to_int cons) new_case
      

  let add_measure t measure =
    (* t.dataMeasureTbl の更新 *)
    let {inputSort = `DataS data;_} = measure in
    let measure_list = Hashtbl.find t.dataMeasuresTbl (Id.to_int data) in
    let () = Hashtbl.replace
               t.dataMeasuresTbl
               (Id.to_int data)
               (measure::measure_list)
    in
    (* t.constructors の更新 *)
    List.iter
      (add_measure_case t measure.name measure.inputSort measure.returnSort)
      measure.matchCases
    
  let add_definition t (def:definition) =
    (* t.datatypesの更新 *)
    let data = def.name in
    let () = Hashtbl.add t.datatypes (Id.to_int data) def in
    (* t.dataMeasuresTblの初期化 *)
    let () = Hashtbl.add t.dataMeasuresTbl (Id.to_int data) [] in
    (* コンストラクタのmeasure_constraintの初期化 *)
    List.iter
      (fun (cons:constructor) ->
        let top_case = top_forumulaCase cons in
        Hashtbl.add t.constructors (Id.to_int cons.name) top_case)
    def.constructors



  let add_refine t (refine:refine) =
    let name = refine.name in
    Hashtbl.add t.refines (Id.to_int name) refine 

  let list_constructor (t:t) data =
    match Hashtbl.find_opt t.datatypes (Id.to_int data)  with
    |Some def -> def.constructors 
    |None -> invalid_arg ("data "^(Id.to_string_readable data)^" not defined")


  let measure_constraint_of_constructor t (`DataS data) cons =
    match Hashtbl.find_opt t.constructors (Id.to_int cons) with
    |Some formula_case ->
      assert (formula_case.constructor = cons);
      formula_case
    |None -> invalid_arg ("constructor "^(Id.to_string_readable cons)^" not defined")

  let termination_measure t (`DataS data) =
    match Hashtbl.find_opt t.dataMeasuresTbl (Id.to_int data) with
    |Some measure_list ->
      List.filter (fun measure -> measure.termination) measure_list
    |None -> invalid_arg ("data "^(Id.to_string_readable data)^" not defined")

  (* [cons] x xs _v = _v = cons x xs && len _v = len xs + 1 *)
  let constructor_specification t (`DataS data) cons =
    let {args = args; body = e;_} =
      measure_constraint_of_constructor t (`DataS data) cons
    in
    let args_es =
      List.map
        (fun (x, sort) ->
          BaseLogic.Var (Hfl.to_baseLogic_sort sort, x))
      args
    in
    let v_eq_cons =
      let open BaseLogic in
      `Base (Eq ((Var ((DataS (data, [])), Id.valueVar_id)),
                 (Cons ((DataS (data, [])),cons, args_es)))
            )
    in
    let pre = List.map (fun _-> `Base (BaseLogic.Bool true)) args in
    Hfl.{params = [];
         args = (args:> (Id.t * Hfl.sort) list);
         body = `Horn (pre, `And (v_eq_cons, `Base e))}
    

           
  let unfold_refine t (cons:constructor) (rdata, real_params) :(Id.t * Hfl.clause) list =
    match Hashtbl.find_opt t.refines (Id.to_int rdata) with
    |None -> assert false
    |Some refine ->
      
      let cases = refine.constructors in (* casesは小さいからlist検索で良いだろう *)
      (match List.find_opt
               (fun (case:refineCase) -> case.constructor = cons.name)
               cases
       with
       |None -> assert false
       |Some {args = args; _} ->

         let subst_param =
           M.add_list2
             (List.map fst refine.param)
             real_params
             M.empty
         in
         let real_args = cons.args in
         let real_args_var =
           (List.map (fun (id, sort)
                      -> `Base (BaseLogic.Var ((Hfl.to_baseLogic_sort sort), id)))
                     real_args)
         in
         let subst_cons_args =
           M.add_list2
             (List.map (fun (x,_,_)->x) args)
             real_args_var
             M.empty
         in
         let subst = M.merge (fun _ _ _ -> assert false)
                           subst_param
                           subst_cons_args
           in
         List.map2
           (fun (x,_) (_, _, clause) ->
             (x, Hfl.subst subst clause))
           real_args
           args
      )

  let rec unfold_clause_diff t z (cons:constructor)= function
      | `Base _ | `Or _| `App _ |`Abs _ -> []
      | `RData (id, params, `Base (BaseLogic.Var (_, z')))
           when z = z' ->
         unfold_refine t cons (id, params)
         |> List.map snd
      | `RData _ -> []
      | `And (c1, c2) -> (unfold_clause_diff t z cons c1)
                         @(unfold_clause_diff t z cons c2)
      
    
  let unfold_clauses_diff t z (cons:constructor) clauses =
    List.fold_left
      (fun acc c -> (unfold_clause_diff t z cons c)@acc)
      []
    clauses
end

    


           
