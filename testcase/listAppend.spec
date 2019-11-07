(* ignore *)

let (==>) a b = (not a) || b
let (&&&)  = (&&)
let (|||) = (||)
let (++) = (@)
type 'a set = 'a list          
(* endignore *)


type list =
  |Nil
  |Cons of int * list
         
let qualifier = [(fun (x:list) (y:list)-> x = y)] 

let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1

let [@measure] rec _elm: list -> int set = function
  |Nil -> []
  |Cons (x, xs) -> _elm xs ++ [x]
    
                 
(* let [@spec dec] d (n:int) (v:int) = *)
(*   (v = (n -1)) *)
                 
let [@spec append] append (l1:list) (l2:list) (v:list)=
  (_len v  = (_len l1) + (_len l2) && _elm v = (_elm l1)++(_elm l2)) 

let append = ??
