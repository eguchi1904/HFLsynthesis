module List = struct
  include List
                                                                                        
  let rec split_tail' l acc_hd =
    match l with
    |[] -> invalid_arg "list:split_tali"
    |[x] -> (acc_hd, x)
    |x::xs -> split_tail' xs (acc_hd@[x])

  let split_tail l = split_tail' l []
    
        
  let rec insert x i l =
    if i = 0 then
      x::l
    else if i > 0 then
      match l with
      |[] -> raise (Invalid_argument "index out of bounds")
      |y::ys -> y :: (insert x (i-1) ys)
    else
      raise (Invalid_argument "index out of bounds")

  let rec diff l1 l2 =        (* l1\l2 *)
    match l1 with
    |x::xs when List.mem x l2 -> diff xs l2
    |x::xs -> x::(diff xs l2)
    |[] -> []


  (* suffix (prefix@sufix) prefix = Some sufix *)
  let rec suffix l prefix =
    match l, prefix with
    |(x::xs),(p::ps)  when x = p ->  suffix xs ps
    |(x::xs),(p::ps) -> None
    |_, [] -> Some l
    |[],(p::ps) -> None

  let rec uniq = function
  |[] -> []
  |x::xs -> if List.mem x xs then uniq xs else x::(uniq xs)

  let rec uniq_f (eq:'a -> 'a -> bool) (l:'a list) =
    match l with
    |x::xs when List.exists (eq x) xs -> uniq_f eq xs
    |x::xs -> x::(uniq_f eq xs)
    |[] -> []

  (* output  (len l2)^(len l1) *)
  let rec enumerate_table (key_list:'a list)
                    (var_list:'b list)
          :('a * 'b) list list = match key_list with
    |key::xs ->
      let key_v_list = List.map (fun var -> (key, var)) var_list  in
      let xs_table_list = enumerate_table xs var_list in
      List.concat
        (List.map
           (fun (key, var) -> List.map (fun table -> (key, var)::table) xs_table_list)
           key_v_list)
    |[] -> []


  let flatten_opt_list l =
    l
    |> List.filter (function Some _  -> true | None -> false)
    |> List.map (function Some s -> s | None -> assert false)

  let assoc_all x table =
    List.filter (fun (y, v) -> x = y) table
    |> List.map snd
          
  let rec pop f = function
    |x::xs when f x -> Some (x, xs)
    |x::xs ->
      (match pop f xs with
       |Some (y, xs') -> Some (y, x::xs')
       |None -> None)
    |[] -> None
          
end

module IntSet =
  Set.Make
    (struct
      type t = int
      let compare = compare
    end)
  

module Combination = struct

  let rec chose m (bag,size) =  (* 前から選んだ組み合わせ *)
    if size < m then []
    else if m <= 0 then [[]]
    else
      match bag with
      |x::xs ->
        let include_x =
          List.map
            (fun l -> x::l)
            (chose (m-1) (xs, (size-1)))
        in
        let exclude_x = chose m (xs, (size-1)) in
        include_x@exclude_x
      |[] -> assert false

  let rec make_bag_rec i n =     
    if i >= n then
      []
    else
      i::make_bag_rec (i+1) n

  let make_bag n =     (* [1;2;...;n-1] *)
    make_bag_rec 1 n
      

  (* 5 [1; 3]  ----> [1; 2; 2] *)
  let split_by_pin n pins =
    match pins with
    |[] -> assert false
    |pin::other ->
      let tail_pin, split' =
        List.fold_left
          (fun (pre_pin, acc) pin ->
            (pin, acc@[(pin - pre_pin)]))
          (pin, [pin])
          other
      in
      split'@[n- tail_pin]
    
  (* not fast. n,m must be smallq q *)
  let split n m =
    if not (m <= n && 0<=m && 1<= n) then
      invalid_arg "Combination.split"
    else if m = 1 then
      [[n]]
    else
      let pins_list = chose (m-1) ((make_bag n),n-1) in
      List.map (split_by_pin n) pins_list

               (* let _ =  chose  2 ([1;2;3;4],4) *)
               (* let _ = split 1 1 *)
  (* let _ = split 3 1 *)
  (*       let _ = split 5 2 *)
  (* let _ = split 6 2 *)
  (* let _ = chose 2 ([1;2;3;4;5],5) *)
      
end
            
