type t


val make:
  Hfl.Equations.t ->
  PathEnv.t ->
  prop: [ `Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list ] ->
  spec: Hfl.qhorn list
  -> t                


val is_valid: t -> bool

val split: (Id.t * Hfl.sort) list -> t -> t * (Id.t * (Hfl.qhorn list)) list

(* 制約を満たす述語割り当てを返す *)
val solve: (Id.t * Hfl.abstSort) list-> t -> (Hfl.abstClause) M.t


val subst: Hfl.clause M.t -> t -> t
