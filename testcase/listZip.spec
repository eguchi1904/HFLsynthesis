type list =
  |Nil
  |Cons of int * list
         


let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1
                 
let [@measure] rec _elm: list -> int set = function
  |Nil -> []
  |Cons (x, xs) -> _elm xs ++ [x]

(* let [@measure] rec _elm: list -> int set = function *)
(*   |Nil -> [] *)
(*   |Cons (x, xs) -> _elm xs ++ [x] *)


type pair_list =
  |PNil 
  |PCons of int * int * pair_list

let[@measure][@termination] rec _plen: pair_list -> int = function
  |PNil -> 0
  |PCons (p1, p2, pxs) -> _plen pxs + 1

let [@measure] rec _pelm: pair_list -> int set = function
  |PNil -> []
  |PCons (x, y, xs) -> _pelm xs ++ [x,y]

                 
let [@spec zip] zip (l1:list) (l2:list) (v:pair_list) =
  ((_len l2) = (_len l1)) ==> (_plen v = _len l1 + _len l2 &&
                                _pelm v = _elm l1 ++ _elm l2)

let zip = ??
