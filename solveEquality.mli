module Env:
sig
  type t
     
  val add: BaseLogic.t -> BaseLogic.t -> t -> t

  (* 単純に同値類に含まれているかを確認する *)
  (* len x = len y を確かめるためにx=yを検討する、などはしない。 *)

  (* TermIdTable.to_id の結果 *)
  val representative: t -> BaseLogic.t -> Id.t
    
  val is_same: t -> BaseLogic.t -> BaseLogic.t -> bool
    
end
     
(* baseLogicの世界で良いのか *)
val f: exists:Id.t list
       -> Env.t
       -> (BaseLogic.t * BaseLogic.t) list
       -> BaseLogic.t M.t option
  