type t

type forallHorn = [ `Horn of Hfl.clause list * Hfl.clause
                  | `Forall of Id.t * Hfl.baseSort * forallHorn]
                

val make:
  Hfl.Equations.t ->
  PathEnv.t ->
  prop: [ `Exists of (Id.t * Hfl.baseSort) list * Hfl.clause list ] ->
  spec: forallHorn list
  -> t                


val is_valid: t -> bool
