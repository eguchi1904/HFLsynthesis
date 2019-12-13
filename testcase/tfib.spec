let qualifier = [(fun (x:int) -> x < 1)]

              
let[@predicate][@mu] fib (n:int) (v:int) =
  exists (v1:int) (v2:int).
     (n <= 1 && v = n)
     |||
       ((fib (n - 1) v1) &&& (fib (n-2) v2) &&& (v = v1 + v2))
    

let [@spec tail_fib] tfib (n:int) (i:int) (a:int) (b:int) (v:int)=
     (fib i a)&&&(fib (i-1) b)&&&(n >= 0)
     ==>
       (fib (n+i) v)

let tail_fib = ??

             
   
