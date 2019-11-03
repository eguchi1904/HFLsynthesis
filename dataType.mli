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
type formulaCase = {constructor: Id.t ; args: (Id.t * Hfl.baseSort) list ; body: BaseLogic.t }
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
   args: (Id.t * Hfl.baseSort * Hfl.clause) list;
  }


type refine = {name: Id.t
              ;param: (Id.t * Hfl.abstSort) list
              ;constructors: refineCase list
              }


module Env:sig

  type t

  val init: unit -> t

  val add_definition: t -> definition -> unit

  val add_measure: t -> measure -> unit

  val add_refine: t -> refine -> unit

  val constructor_specification: t -> [`DataS of Id.t ] -> Id.t -> Hfl.fhorn

  val fold_datatype:(Id.t ->definition ->'a ->'a) ->t ->'a ->'a

  val list_constructor: t -> Id.t ->  constructor list

  val measure_constraint_of_constructor: t -> [`DataS of Id.t] -> Id.t -> formulaCase
    
  (* list なら、 len  など、
     停止性を保証するために使って良い下限のあるint型を返すmeasure
     ユーザがannotate
   *)
  val termination_measure: t -> [`DataS of Id.t] -> measure list


  (* 
     List (\x.x>0) (y::ys)
     から 、
     y > 0 && List (\x.x>0) ys 
     と展開し、y,ysに要求される条件を生成する

   *)
  val unfold_refine: t -> constructor -> Id.t * Hfl.abstClause list -> (Id.t * Hfl.clause) list

  (* unfold_clause_diff x (Cons y ys) \phi(x)
     -> \phi(y::ys)

     invaliant: not (x \in FV{unfold_clause_diff x ...)} )
   *)
  val unfold_clauses_diff: t -> Id.t -> constructor -> Hfl.clause list->  Hfl.clause list



end



