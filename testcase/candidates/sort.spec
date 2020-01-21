type list =
  |Nil
  |Cons of int * list

let [@predicate] sorted (l:list) =
  exists (x:int)  (xs:list) (y:int) (ys:list).
  (l = Nil)
  |||
    (l = Cons x Nil)
  |||
    ((l = Cons x xs) &&& (xs = Cons y ys) &&& (x < y) &&& (sorted xs))


let [@spec insert] insert (x:int) (l:list) (v:list) =
  (sorted l) ==> ((sorted v) && (elem v = elem l ++ [x]))




let rec insert x l =
  match l with
  |[] -> [x]
  |y::ys ->
    if x <= y then
      Cons x l
    else
      Cons y (insert x ys)



sorted l && l = y::ys && y < x
--------------------------------------------------
  Cons ?z ?zs => (sorted v) && (elem v = elem l ++ [x])


(sorted (z::zs)) && (elem z::zs = elem l ++ [x])



