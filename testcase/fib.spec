

let qualifier = [(fun (x:int) -> x <= 1)]

              
let[@predicate][@mu] fib (n:int) (v:int) =
  exists (v1:int) (v2:int).
  (n = 0 && v = 0)
 |||( n = 1 && v = 1)  
     |||
       ((fib (n-1) v1) &&& (fib (n-2) v2)&&&(v = v2 + v1))
    

let[@spec fib] fib (n:int) (v:int)=
      (n >= 0) ==> fib n v
     
     

let fib = ??


   
                       
                   
   
