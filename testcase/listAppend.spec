(* ignore *)

let (==>) a b = (not a) || b
let (&&&)  = (&&)
let (|||) = (||)              
(* endignore *)


type list =
  |Nil
  |Cons of int * list
         
let qualifier = [(fun (x:list) (y:list)-> x = y)] 

let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1

(* let [@spec dec] d (n:int) (v:int) = *)
(*   (v = (n -1)) *)
                 
let [@spec append] append (l1:list) (l2:list) (v:list)=
  (_len v  = (_len l1) + (_len l2))

let append = ??
