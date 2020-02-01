type list =
  |Nil
  |Cons of int * list
         
let qualifier = [(fun (x:int) (y:int) -> x <= y);(fun (x:list) (y:list)-> x = y)] 

let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1


let [@measure] rec _elm: list -> int set = function
  |Nil -> []
  |Cons (x, xs) -> _elm xs ++ [x]


let [@predicate][@mu] sorted (l:list) =
  exists (x:int) (xs:list)  (y:int) (ys:list).
  (l = Nil)
  |||((l = Cons x xs) &&& (sorted xs) &&& ((xs = Nil) ||| ((xs = Cons y ys) &&& (x <= y))))

let[@spec insert] insert (l:list) (x:int) (v:list) = 
  (sorted l) ==> (sorted v) &&& (_elm v = (_elm l)++[x])

let insert = ??
  


