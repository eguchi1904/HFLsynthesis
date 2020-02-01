(* ignore *)
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

type listlist =
  |NNil
  |CCons of list * listlist
                 
(* let [@spec dec] d (n:int) (v:int) = *)
(*   (v = (n -1)) *)

let[@measure] rec _count (l:list) (elm:int) :int =
  match l with
  |Nil -> 0
  |Cons (x,xs) -> if x = elm then
                    1 + _count xs elm
                  else
                    _count xs

let [@measure] rec _mem (l:list) (elm:int) :bool =
  match l with
  |Nil -> false
  |Cons (x,xs) -> if x = elm then
                    true
                  else
                    _mem xs elm

let append (l1:list) (l2:list) (v:list) =
  Exists ((xs_l2:list),
          match l1 with
          | Nil -> v = l2
          | Cons (x,xs) ->
             append xs l2 xs_l2 && v = Cons (x, xs_l2)
         )




let[@spec split][@mu] split (l:list) (del:int) (v:listlist)
  =
  Exists ((l':list),
          _llen v = _count l del + 1
          && match v with
             | NNil -> false
             | CCons (g, gs) ->
                (not _mem g del)
                  && match gs with
                     | NNil -> l = g 
                     | CCons (_,_) -> 
                        split l' del gs && append g (del::l') l
         )

  

let append = ??
