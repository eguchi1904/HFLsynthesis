

let rec [@predicate][@mu] mul x y z =
  (y = 0 && z = 0)
  ||(mul x (y-1) (z-y) )

  

let [@spec div] div (n:int) (m:int) (v:intpair) =
  match v with
    (q,r) -> mul m q (n - r)n&& 0 < r < m

  
