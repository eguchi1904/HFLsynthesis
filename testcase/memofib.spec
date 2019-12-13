

type list =
  |Nil
  |Cons of int * list

let qualifier = [(fun (x:int) -> x <= 1)]
              
let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1


let[@predicate][@mu] fib (n:int) (v:int) =
  exists (v1:int) (v2:int).
     (n <= 1 && v = n)
     |||
       ((fib (n - 1) v1) &&& (fib (n-2) v2) &&& (v = v1 + v2))
    

(* [fib(0)....fib(n)]を返す *)
let[@predicate][@mu] fib_list (n:int) (l:list) =
exists (x:int) (xs:list).
  (n < 0 && l = Nil)
  |||
  (l = Cons x xs &&& fib n x &&& fib_list (n-1) xs)
  


let[@spec memo_fib] fib_memo (n:int) (l:int) =
      (n >= 0) ==> fib_list n l



    

(* (\* これがでたら良い *\) *)
let rec fib_memo n =
  if n < 0 then Nil
  else
    match fib_memo (n-1) with
    |Nil -> Cons n Nil
    |(Cons x xs as l)->
       (match xs with
         |Nil -> Cons n l
         |Cons y ys -> Cons (x+y) l)

(* または、 *)
let rec fib_memo n = 
  if n < 0 then Nil
  else if n <= 1 then Cons n Nil
  else
    match fib_memo (n-1) with
    |Nil -> assert false
    |(Cons x xs as l)->
       (match xs with
         |Nil -> Cons n l
         |Cons y ys -> Cons (x+y) l)


    
  
