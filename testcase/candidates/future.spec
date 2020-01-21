type list =
  |Nil
  |Cons of int * list

type listlist =
  |NNil
  |CCons of list * listlist

let[@measure][@termination] rec _len: list -> int = function
  |Nil -> 0
  |Cons (x, xs) -> _len xs + 1

let[@measure][@termination] rec _llen: list -> int = function
  |NNil -> 0
  |CCons (x, xs) -> _llen xs + 1


(* ************************************************** *)
(* suffix *)
(* ************************************************** *)                   
let[@predicate] is_suffix l suf =
  (len suf <= len l)            (* 必要。back-endが協力なら *)
  &&
    ((l = suf)
     |||
       (match l with
        |x::xs -> suffix xs suf)
    )

  
let[@refine-predicate] rec rLIST (p:int -> bool) (r:int-> int -> bool) = function
  |Nil -> true
  |Cons (x, xs) -> p x &&&  (rLIST (fun (x':int) -> p x' &&& r x x')
                                   (fun (x:int) (y:int) -> r x y) (* *)
                                   xs
                            )

let[@spec gen_suffix] gen_suffix (l:list) (v:listlist) =
  _llen v = _len l + 1
  &&&(rList (fun elm -> is_suffix l elm) (fun elm_i elm_j -> elm_i <> elm_j)　v)
    
(* ************************************************** *)
(* tail recursive fib *)
(* ************************************************** *)
let[@predicate][@mu] fib (n:int) (v:int) =
  Exists
    ([(v1:int) (v2:int)],
     (n <= 1 && v = n)
     |||
       ((fib (n - 1) v1) &&& (fib (n-2) v2) &&& v = v1 + v2)
    )

let [@spec tail_fib] tfib (n:int)　(a:int)　(b:int) (v:int)=
  Forall
    ([(i:int)],
     (fib i a)&&&(fib (i-1) b)&&(n >= 0)
     ==>
       (fib (n+i) v)
    )

let rec tail_fib n a b  =
  if n < 1 then
    a
  else
    tail_fib  (n-1) (a+b) a


(* ************************************************** *)
(* tail recursive fib *)
(* ************************************************** *)
let[@predicate][@mu] fib (n:int) (v:int) =
  Exists
    ([(v1:int) (v2:int)],
     (n <= 1 && v = n)
     |||
       ((fib (n - 1) v1) &&& (fib (n-2) v2) &&& v = v1 + v2)
    )

let [@spec tail_fib] tfib (n:int)　(i:int) (a:int)　(b:int) (v:int)=
     (fib i a)&&&(fib (i-1) b)&&(n >= 0)
     ==>
       (fib (n+i) v)

   
(* 現実的な時間に出てくるかなkore
 *)
let rec tail_fib n i a b  =
  if n < 1 then
    a
  else
    tail_fib (n-1) (i+1) (a+b) a



(* ************************************************** *)
(* memo fib *)
(* ************************************************** *)
  




  
(* ************************************************** *)
(* 会場 *)
(* ************************************************** *)  

let [@predicate][@mu] sum (n:int) (v:int) =
  Exist([(v1:int)],
        (n <= 1 && v = n)
        |||((sum (n-1) v1) && v = v1 + n)
       )
  
  
(* ************************************************** *)
(* split_str *)
(* ************************************************** *)

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
  
