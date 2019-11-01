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
type formulaCase = {constructor: Id.t ; args: Id.t list ; body: BaseLogic.t }
type measure = {name: Id.t
               ;termination: bool
               ;inputSort: [`DataS of Id.t]
               ;returnSort: Hfl.baseSort
               ;matchCases: formulaCase list}


             
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

    
  let add_measure_case
        (case:formulaCase)
        t
    =
    match Hashtbl.find_opt t.constructors (Id.to_int cons) with
    |None -> Hashtbl.add t.constructors (Id.to_int cons)  case
    |Some measure_constraint ->
      

    

  let add_measure measure t =
    (* t.dataMeasureTbl の更新 *)
    let {inputSort = `DataS data;_} = measure in
    let measure_list = Hashtbl.find t.dataMeasuresTbl (Id.to_int data) in
    let () = Hashtbl.replace
               t.dataMeasuresTbl
               (Id.to_int data)
               (measure::measure_list)
    in
    (* t.constructors の更新 *)
    List.iter add_measure_case measure.matchCases
    
    

  let list_constructor (t:t) data =
    match Hashtbl.find_opt t.datatypes (Id.to_int data)  with
    |Some def -> def.constructors 
    |None -> invalid_arg ("data "^(Id.to_string_readable data)^" not defined")


  let measure_constraint_of_constructor t (`Data data) cons =
    match Hashtbl.find_opt t.constructors (Id.to_int cons) with
    |Some formula_case ->
      assert (formula_case.constructor = cons);
      formula_case
    |None -> invalid_arg ("constructor "^(Id.to_string_readable cons)^" not defined")

  let termination_measure t (`Data data) =
    match Hashtbl.find_opt t.dataMeasuresTbl (Id.to_int data) with
    |Some measure_list ->
      List.filter (fun measure -> measure.termination) measure_list
    |None -> invalid_arg ("data "^(Id.to_string_readable data)^" not defined")

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

    


           
