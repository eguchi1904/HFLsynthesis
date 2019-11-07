(* ignore *)

let (==>) a b = (not a) || b
let (&&&)  = (&&)
let (|||) = (||)
let (++) = (@)
type 'a set = 'a list
(* endignore *)

let qualifier = [(fun (x:int) -> x < 1)]

type list =
  |Nil
  |Cons of int * list
         

let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1


                 
let [@spec dec] d (n:int) (v:int) =
  (v = (n -1))
                 
let [@spec rep] rep (n:int) (v:list) =
  (n >= 0) ==> (_len v = n) 

let rep = ??


  
                 
