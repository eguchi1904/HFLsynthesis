open FptSynthesis
   
module TestSolveEquality = struct
  open BaseLogic
  let result_to_string = function
    |None -> "no solution"
    |Some sita ->
      M.fold
        (fun i e acc ->
          (Id.to_string_readable i)^"-->"^(BaseLogic.p2string e)^"; "^acc)
        sita
        ""
     
  let test1 () =
    let i = Id.genid_const "i" in
    let i' =  Id.genid_const "i'" in
    let n = Id.genid_const "n" in
    let i_var = Var (IntS, i) in
    let i'_var = Var (IntS, i') in
    let n_var = Var (IntS, n) in
    let e1 = Plus (Minus (n_var, Int 1), i'_var) in
    let e2 = Plus (n_var, i_var) in
    let env = SolveEquality.Env.empty in
    let result =
      SolveEquality.f ~exists:[i'] env [(e1, e2)]
    in
    "result:TEST1\n"^result_to_string result |> print_string
    
    
  let f () = List.iter (fun f -> f ()) [test1]
           
           
end

                         
let _ =
  TestSolveEquality.f ()
