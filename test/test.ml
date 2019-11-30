open FptSynthesis


module TestPolynomial = struct
  open BaseLogic
  let test1 () = 
    let i = Id.genid_const "i"  in
    let i' =  Id.genid_const "i'" in
    let n = Id.genid_const "n" in
    let i_var = Var (IntS, i) in
    let i'_var = Var (IntS, i') in
    let n_var = Var (IntS, n) in
    let e1 = Plus (Minus (n_var, Int 1), i'_var) in (* (n -1)+i' *)
    let e1' = Minus (Plus (n_var, i'_var), Int 1) in (* (n+i')-1 *)
    let e1'' = Plus (Plus (i'_var, Int 1), Minus (n_var, Int 2)) in (* (i'+1)+(n -2) *)
    let e2 = Plus (n_var, i_var) in
    match Polynomial.of_term e1 with
    |None -> assert false
    |Some e1_polly ->
      (match Polynomial.of_term e1' with
       |None -> assert false
       |Some e1'_polly ->
         (match Polynomial.of_term e1'' with
          |None -> assert false
          |Some e1''_polly ->
            (match Polynomial.of_term e2 with
             |None -> assert false
             |Some e2_polly ->
               (assert (Polynomial.equal e1_polly e1'_polly));
               (assert (Polynomial.equal e1'_polly e1''_polly));
               (assert (not (Polynomial.equal e1_polly e2_polly)));
               (print_string "TestPolynomial.TEST1 SUCSESS\n")
            )
         )
      )


  let f () = List.iter (fun f -> f ()) [test1]     

end

                      
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

  let problem_to_string e1 e2 =
    (BaseLogic.p2string e1)^" = "^(BaseLogic.p2string e2)
     
  let test1 () =
    let i = Id.genid_const "i" in
    let i' =  Id.genid_const "i'" in
    let n = Id.genid_const "n" in
    let i_var = Var (IntS, i) in
    let i'_var = Var (IntS, i') in
    let n_var = Var (IntS, n) in
    let e1 = Plus (Minus (n_var, Int 1), i'_var) in(* (n+i')-1 *)
    let e2 = Plus (n_var, i_var) in                (* n+i *)
    let env = SolveEquality.Env.empty in
    let result =
      SolveEquality.f ~exists:[i'] env [(e1, e2)]
    in
    "result of"^(problem_to_string e1 e2)^"\n"^result_to_string result |> print_string
    
    
  let f () = List.iter (fun f -> f ()) [test1]
           
           
end

                         
let _ =
  let () = TestPolynomial.f () in
  let () =  TestSolveEquality.f () in
  ()
