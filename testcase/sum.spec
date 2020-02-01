let qualifier = [(fun (x:int) -> x <= 0)]
              
let[@predicate][@mu] sum (n:int) (v:int) =
  exists (v1:int).
  (n = 0 && v = 0)
  ||| ((sum (n-1) v1) &&& (v = v1 + n))


let[@spec sum] f (n:int) (v:int) =
  (n >= 0) ==> sum n v

(* let[@spec acc_sum] acc_sum (i:int) (a:int)(n:int) (v:int) =
 *   (n >= 0) &&& (sum i a) ==> (sum (i+n) v) *)
  
let sum =  ??

