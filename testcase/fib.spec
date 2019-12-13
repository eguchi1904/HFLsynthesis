

let qualifier = [(fun (x:int) -> x <= 1)]

              
let[@predicate][@mu] fib (n:int) (v:int) =
  exists (v1:int) (v2:int).
     (0 <= n && n <= 1 && v = n)
     |||
       ((v = v2 + v1) &&& (fib (n - 1) v1) &&& (fib (n-2) v2))
    




let[@spec fib] fib (n:int) (v:int) =
      (n >= 0) ==> fib n v
     
     

let fib = ??


   
                       
                   
   
