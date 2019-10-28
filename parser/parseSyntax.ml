let sort_unfix = BaseLogic.DataS (Id.genid_const "unfix", [])



type constructor = {name:Id.t;
                    args:Hfl.baseSort list (* (int *  ) -> *)
                   }
type typedef = {name: Id.t
               ;constructors: constructor list}
                 


type predicateArg =
  {name: Id.t;
   is_param: bool;
   sort: Hfl.sort}

  
(* Hfl.clauseとapplicationの部分が違う。parameter等の区別なし。HFl自体もそれで良いのでは？
*)
type  clause = (*\psi(x,y): predicate type formula *)
  [ `Base of BaseLogic.t
  | `Abs of ((Id.t * Hfl.sort) list * clause)(* 1階の場合は使わない *)           
  | `App of application
  | `RData of Id.t * abstClause list * clause (* List (\x.x>0) _v みたいな述語。 実装上特別扱い*)
  (* |Unknown of Id.t * sort  (\* unknown predicate *\) *)
  | `Or of clause * clause
  | `And of clause * clause
  ]
  and application =  {head:Id.t;
                      args:clause list}

  and  abstClause = [`Abs of (Id.t * Hfl.sort) list * clause]
                  


  
type predicateDef = (* F x =mu \phi(x) => \phi(x, F) の形*)
  {name: Id.t;
   args: predicateArg list;
   fixpoint: Hfl.fixOp option;
   body: clause option * clause
  }
         

type refineCase = {name:Id.t;
                   args:Id.t list;
                   body:BaseLogic.t}
                
type refinePredicate =  {name: Id.t;
                         param: predicateArg list;
                         cases: refineCase list}
                        

type elm =
  | QualifierDef of Qualifier.t list
  | DataDef of typedef
  | MeasureDef of DataType.measure
  | RefinePredicateDef of refinePredicate
  | PredicateDef of predicateDef             
  | VarSpecDec of (Id.t * predicateDef)
  | Goal of Id.t


type t = elm list

  
