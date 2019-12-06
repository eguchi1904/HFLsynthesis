(* open FptSynthesis *)


(* module TestPolynomial = struct *)
(*   open BaseLogic *)
(*   let test1 () =  *)
(*     let i = Id.genid_const "i"  in *)
(*     let i' =  Id.genid_const "i'" in *)
(*     let n = Id.genid_const "n" in *)
(*     let i_var = Var (IntS, i) in *)
(*     let i'_var = Var (IntS, i') in *)
(*     let n_var = Var (IntS, n) in *)
(*     let e1 = Plus (Minus (n_var, Int 1), i'_var) in (\* (n -1)+i' *\) *)
(*     let e1' = Minus (Plus (n_var, i'_var), Int 1) in (\* (n+i')-1 *\) *)
(*     let e1'' = Plus (Plus (i'_var, Int 1), Minus (n_var, Int 2)) in (\* (i'+1)+(n -2) *\) *)
(*     let e2 = Plus (n_var, i_var) in *)
(*     match Polynomial.of_term e1 with *)
(*     |None -> assert false *)
(*     |Some e1_polly -> *)
(*       (match Polynomial.of_term e1' with *)
(*        |None -> assert false *)
(*        |Some e1'_polly -> *)
(*          (match Polynomial.of_term e1'' with *)
(*           |None -> assert false *)
(*           |Some e1''_polly -> *)
(*             (match Polynomial.of_term e2 with *)
(*              |None -> assert false *)
(*              |Some e2_polly -> *)
(*                (assert (Polynomial.equal e1_polly e1'_polly)); *)
(*                (assert (Polynomial.equal e1'_polly e1''_polly)); *)
(*                (assert (not (Polynomial.equal e1_polly e2_polly))); *)
(*                (print_string "TestPolynomial.TEST1 SUCSESS\n") *)
(*             ) *)
(*          ) *)
(*       ) *)


(*   let f () = List.iter (fun f -> f ()) [test1]      *)

(* end *)

                      
(* module TestSolveEquality = struct *)
(*   open BaseLogic *)
(*   let result_to_string = function *)
(*     |None -> "no solution" *)
(*     |Some sita -> *)
(*       M.fold *)
(*         (fun i e acc -> *)
(*           (Id.to_string_readable i)^"-->"^(BaseLogic.p2string e)^"; "^acc) *)
(*         sita *)
(*         "" *)

(*   let problem_to_string e1 e2 = *)
(*     (BaseLogic.p2string e1)^" = "^(BaseLogic.p2string e2) *)
     
(*   let test1 () = *)
(*     let i = Id.genid_const "i" in *)
(*     let i' =  Id.genid_const "i'" in *)
(*     let n = Id.genid_const "n" in *)
(*     let i_var = Var (IntS, i) in *)
(*     let i'_var = Var (IntS, i') in *)
(*     let n_var = Var (IntS, n) in *)
(*     let e1 = Plus (Minus (n_var, Int 1), i'_var) in(\* (n+i')-1 *\) *)
(*     let e2 = Plus (n_var, i_var) in                (\* n+i *\) *)
(*     let env = SolveEquality.Env.empty in *)
(*     let result = *)
(*       SolveEquality.f ~exists:[i'] env [(e1, e2)] *)
(*     in *)
(*     "result of"^(problem_to_string e1 e2)^"\n"^result_to_string result |> print_string *)
    
    
(*   let f () = List.iter (fun f -> f ()) [test1] *)
           
           
(* end *)

module TestSeq = struct

  module Seq = Base.Sequence
             
  let mk_seq1 () =
    Seq.singleton
      (let () = print_string "mk_element!\n" in
       1)

  let mk_seq2 () =
    Seq.concat_map
      (Seq.singleton 1)
      ~f:(fun _ ->
        let () = print_string "mk_element\n" in
        Seq.singleton 1)

  let mk_seq n step m =
    Seq.unfold
      ~init:(n, 0)
      ~f:(fun (n', size) ->
        if size > m then None
        else
          let () = Printf.printf "making %d!! \n" n' in
          Some (n', ((n'+step), size+1)))

  let rec mk_seq_list n size =  (* [0,1,2],[100,101,201].....] *)
    if size <= 0 then []
    else
      (mk_seq n 1 10)::(mk_seq_list (n+100) (size -1))

  let rec rep a n =
    if n <= 0 then []
    else
      a::(rep a (n-1))
    
  let test_fold () =
    let size = 10 in
    let size_of_each_list = 10 in
    let seq_list_seq =
      Seq.unfold
        ~init:0
        ~f:(fun n ->
          if n >= size then None
          else
            let () = print_string "mk_seq list!\n" in      
            Some ((mk_seq_list (10*n) size_of_each_list), n+1))
    in
    let seq_list =
      Seq.fold
        seq_list_seq
        ~init:(rep Seq.empty size_of_each_list)
        ~f:(fun acc seq_list->
          List.map2 (fun seq1 seq2 -> Seq.append seq1 seq2) acc seq_list)
    in
    let seq =
      List.fold_right
        (fun t acc -> Seq.append t acc)
        seq_list
      Seq.empty
    in
    let () = print_string "will print\n" in
    let () = Seq.iter seq ~f:(fun i -> print_int i; print_newline ()) in
    ()
      
    
        
    
    

  let f () =
    let () = test_fold () in
    let () = print_string "\nwill make seq1\n" in
    let seq1 = mk_seq1 () in
    let () = print_string "will make seq2\n" in
    let seq2 = mk_seq2 () in
    let () = print_string "print seq1\n" in
    let () = Seq.iter seq1 ~f:(fun i -> print_int i; print_newline ()) in
    let () = print_string "print seq2\n" in
    let () = Seq.iter seq2 ~f:(fun i -> print_int i; print_newline ()) in    
    ()
end
    


    
  
                         
let _ =
  (* let () = TestPolynomial.f () in *)
  (* let () =  TestSolveEquality.f () in *)
  let () =  TestSeq.f () in  
  ()
