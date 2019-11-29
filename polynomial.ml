open BaseLogic
open Extensions.OptionMonad

   
type t = int M.t * int


let is_zero (map, const) =
  const = 0 && (M.for_all (fun _ c -> c = 0) map)
  
let mult c (map, const) =
  let map' = M.map (fun i -> c*i) map in
  let const' = c*const in
  (map', const')


let add (map1, const1) (map2, const2) =
  let map = M.union
              (fun _ i1 i2 -> Some (i1+i2))
              map1
              map2
  in
  (map, const1 + const2)


let minus (map1, const1) (map2, const2) =
  let map = M.union
              (fun _ i1 i2 -> Some (i1 - i2))
              map1
              map2
  in
  (map, const1 - const2)


let elminate_zero (map, const) = 
  let map = M.filter (fun _ c -> c <> 0) map in
  (map, const)
  

let neg (map, const) =
  let map = M.map (fun i -> -i) map in
  (map, -const)

let rec of_term = function
  |Int i -> return (M.empty, i)
  |UF _ ->  None
  |Times (t1, t2) ->
    of_term t1 >>=
      (fun (map1, const1) ->
        of_term t2 >>=
          (fun (map2, const2) ->
            if M.is_empty map1 then (* t1 is scalar *)
              return (mult const1 (map2, const2))
            else if M.is_empty map2 then(* t2 is scalar *)
              return (mult const2 (map1, const1))
            else
              None
          )
      )
  |Plus (t1, t2) -> 
    of_term t1 >>=
      (fun poly1 ->
        of_term t2 >>=
          (fun poly2 ->
            return (add poly1 poly2)
          )

      )
  |Minus (t1, t2) -> 
    of_term t1 >>=
      (fun poly1 ->
        of_term t2 >>=
          (fun poly2 ->
            return (minus poly1 poly2)
          )

      )            
  |Neg t1 ->
    of_term t1 >>=
      (fun poly1 -> return (neg poly1))

  | _ -> None


let to_term (map, const) =
  M.fold
    (fun id c acc ->
      if acc = Int 0 then
        Times (Int c, Var (IntS, id))
      else
        Plus (Times (Int c, Var (IntS, id)), acc))
    map
    (Int const)


let solve_poly_eq_zero_by_specific_var var (map,const) =
  M.find_opt var map >>= (fun c_var ->
    let migrated_map =
      M.filter (fun id _ -> id <> var) map
      |> M.map (fun c -> -c)
    in
    let migrated_const = -const in
    if M.for_all (fun _ c -> (abs c) mod (abs c_var) = 0) migrated_map
       && (abs migrated_const) mod (abs c_var) = 0
    then
      Some ((M.map (fun c -> c/c_var) map), migrated_const/c_var)
    else
      None
  )

  
(* map <> 0 *)
let rec solve_poly_eq_zero ~exists poly =
  match exists with
  |[] -> None
  |x::xs ->
    match solve_poly_eq_zero_by_specific_var x poly with
    |None -> solve_poly_eq_zero ~exists:xs poly
    |Some solution ->  Some (M.singleton x solution)
  

let solve_eq ~exists poly1 poly2 =
  let poly = minus poly1 poly2
             |> elminate_zero
    in
    if is_zero poly then
      Some M.empty
    else
       solve_poly_eq_zero ~exists poly 

    
    
    

       

  
