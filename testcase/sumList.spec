type list =
  |Nil
  |Cons of int * list

let qualifier = [(fun (l:list) -> l = Nil);(fun (x:int) -> x <= 0)]

              
let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1
              
              
let[@predicate][@mu] sum (n:int) (v:int) =
  exists (v1:int).
  (n = 1 && v = n)
  ||| ((sum (n-1) v1) &&& (v = v1 + n))


let[@predicate][@mu] sum_list (n:int) (l:list) =
  exists (x:int) (xs:list).
  (n <= 0 && l = Nil)
  |||
    ((l = Cons x xs) &&& sum n x &&& sum_list (n-1) xs)

let [@spec dec] d (n:int) (v:int) =
  (v = (n - 1))

let [@spec add] add (n:int) (m:int) (v:int) =
  (v = (n + m))  
  
let[@spec memo_sum] memo_sum (n:int) (l:list) =
  (n >= 0) ==> sum_list n l



  
let memo_sum =  ??

                  (* memo_sum n = *)
                  (* if n< = 0 then n *)
                  (* else *)
                  (*   match memo_sum (n-1) with
                         |Nil -> Cons n Nil
                         |Cons y ys -> Cons (y+n) a
  *)
