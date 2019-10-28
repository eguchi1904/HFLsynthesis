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
   args: (Id.t * Hfl.baseSort * BaseLogic.t) list;
  }


type refine = {name: Id.t
              ;param: (Id.t * Hfl.abstSort)
              ;constructors: refineCase list
              }


module Env:sig

  type t

  val list_constructor: t -> Id.t ->  constructor list

  val measure_constraint_of_constructor: t -> [`Data of Id.t] -> Id.t -> formulaCase

  val termination_measure: t -> [`Data of Id.t] -> Id.t
  (* list なら、 len  など、
     停止性を保証するために使って良い下限のあるint型を返すmeasure
     ユーザがannotate
   *)

  (* 
     List (\x.x>0) (y::ys)
     から 、
     y > 0 && List (\x.x>0) ys 
     と展開し、y,ysに要求される条件を生成する

   *)
  val unfold_refine: t -> constructor -> Id.t * Hfl.abstClause list -> (Id.t * BaseLogic.t) list

  (* unfold_clause_diff x (Cons y ys) \phi(x)
     -> \phi(y::ys)

     invaliant: not (x \in FV{unfold_clause_diff x ...)} )
   *)
  val unfold_clauses_diff: t -> Id.t -> constructor -> Hfl.clause list->  Hfl.clause list



end



