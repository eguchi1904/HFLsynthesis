(* ignore *)

let (==>) a b = (not a) || b
let (&&&)  = (&&)
let (|||) = (||)              
(* endignore *)

          
let qualifier = [(fun (x:int) (y:int) -> x =  y ) ; (fun (x:int) (y:int) -> x > y)]

type list =
  |Nil
  |Cons of int * list

let[@measure] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1

                 
let[@refine-predicate] rec rLIST (p:int -> bool) (r:int-> int -> bool) = function
  |Nil -> true
  |Cons (x, xs) -> p x &&&  (rLIST (fun (x':int) -> p x' &&& r x x')
                                   (fun (x:int) (y:int) -> r x y) (* *)
                                   xs
                            )

let [@predicate][@nu] rec _P (x:int) =  (x = 0)&&&(_P (x+2))

                                     
let[@spec sort] sorting (p[@param]:int->bool) (l:list) (v:list) =
  rLIST (fun (x:int) -> p x) (fun (x:int) (y:int) -> true) l
  ==>
    (rLIST (fun (x:int) -> p x) (fun (x:int) (y:int) -> (x < y)) v )
  &&& (_len v = _len l)


let sort = ??


