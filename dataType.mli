type constructor = {name: Id.t;
                    args: (Id.t * Hfl.baseSort * BaseLogic.t) list;
                    return: [`DataS of Id.t]
                   }
                 
type t = {name: Id.t
         ;param: (Id.t * Hfl.abstSort)
         ;constructors: constructor list
         }


       
module Env:sig

  type t

  val list_constructor: Id.t -> constructor list

end
