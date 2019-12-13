type list =
  |Nil
  |Cons of int * list
         
let qualifier = [(fun (x:int) (y:int) -> x = y);(fun (x:list) (y:list)-> x = y)] 

let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1


let [@measure] rec _elm: list -> int set = function
  |Nil -> []
  |Cons (x, xs) -> _elm xs ++ [x]
    
                 
let [@spec delete] delete (x:int) (l:list) (v:list)=
  (_elm v = (_elm l)--[x])

let delete = ??
