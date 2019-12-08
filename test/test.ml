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


  let test2 () =
    let n = Id.genid_const "n" in
    let n_var = Var (IntS, n) in    
    let env = SolveEquality.Env.empty
              |> SolveEquality.Env.add (Int 0) n_var
    in
    match SolveEquality.f ~exists:[] env [(Int 0, n_var)] with
    |None -> assert false
    |Some sita ->
      if M.is_empty sita then
        print_string "\nSUCSESS test2: 0=n imply n=0\n"
      else
        assert false
    

  (*  0<=n && n <= 0 imply 0? *)
  let test3 () =
    let n = Id.genid_const "n" in
    let n_var = Var (IntS, n) in    
    let env = SolveEquality.Env.empty
              |> SolveEquality.Env.add_lower_bound (Int 0) n
              |> SolveEquality.Env.add_upper_bound  n (Int 0)
    in
    match SolveEquality.f ~exists:[] env [(n_var, Int 0)] with
    |None -> assert false
    |Some sita ->
      if M.is_empty sita then
        print_string "\nSUCSESS test3: 0<=n && n <= 0 imply n= 0\n"
      else
        assert false

    
  let f () = List.iter (fun f -> f ()) [test1; test2; test3]
           
           
end


module TestConstraint = struct


  
end

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


module TestSSeq = struct
  module Seq = Base.Sequence
  module SSeq =  (val (SortedSequence.generator ~size_max:10))
               
  let print_list l =
    let elm_str =
      List.map (fun i -> string_of_int i) l
    |> String.concat ";"
    in
    print_string ("["^elm_str^"]")

  let rec mk_list i ~len =
    if len <= 0 then []
    else
      i :: (mk_list (i+1) ~len:(len -1))

  let mk_list i ~len =
    let l = mk_list i ~len in
    let () = (print_string "make list:" );
             (print_list l);
             (print_newline ())
    in
    l
    

  let mk_same_len_list_seq ~len ~num start =
    Seq.unfold
      ~init:start
      ~f:(fun i ->
        if i >= start + num*len then None
        else
          Some ((mk_list i ~len), (i + len)))
    |> Seq.memoize


  let mk_sseq start =           (* [[ 100],[101],[102]]; [[100;101];[100;102]..] *)
    SSeq.empty
    |> SSeq.append_sequence (mk_same_len_list_seq ~len:1 ~num:3 start) ~size:1
    |> SSeq.append_sequence (mk_same_len_list_seq ~len:2 ~num:3 start) ~size:2
    |> SSeq.append_sequence (mk_same_len_list_seq ~len:3 ~num:3 start) ~size:3


  let mk_sorted_len_list_seq start ~num = (* [1],[2,3],[4,5,6]... *)
    Seq.unfold
      ~init:(1, start)
      ~f:(fun (i, start) ->
        if i >= num then None
        else
          Some ((mk_list start ~len:i), (i+1, start+i)))

    
    
  let test_concat () =
    (* [1],[2,3],[4,5,6]... *)
    let seq_sorted = mk_sorted_len_list_seq 1 ~num:5
                     |> Seq.memoize
    in
    (* [[ 100],[101],[102]]; [[100;101];[100;102]..] *)    
    let sseq = mk_sseq 100 in
    let sseq_seq =
      Seq.map
        seq_sorted
        ~f:(fun l ->
          SSeq.map
            sseq
            ~f:(fun l' -> l@l')
            ~size_diff:(List.length l))
    in
    let result_sseq = SSeq.concat sseq_seq ~min_size:2 in
    let result_seq = (SSeq.to_seq result_sseq) in
    let () = print_string "print result\n" in
    let () = Seq.iter
               result_seq
           ~f:(fun l -> print_list l; print_newline ())
      in
    ()


  let test_concat2 () =
    let seq_sorted = mk_sorted_len_list_seq 1 ~num:5
                     |> Seq.memoize
    in    
    let sseq_seq =
      Seq.map
      seq_sorted
      ~f:(fun _ ->
        mk_sseq 100)
    in
    let result_sseq = SSeq.concat sseq_seq ~min_size:1 in
    let () = print_string "print result\n" in
    let () = Seq.iter
           (SSeq.to_seq result_sseq)
           ~f:(fun l -> print_list l; print_newline ())
    in
    ()    
    
    
    
 let test_concat3 () =
    (* [1],[2,3],[4,5,6]... *)
    let seq_sorted = mk_sorted_len_list_seq 1 ~num:5 in
    (* [[ 100],[101],[102]]; [[100;101];[100;102]..] *)    
    let sseq = mk_sseq 100 in
    let sseq_seq =
      Seq.map
        seq_sorted
        ~f:(fun l ->
          SSeq.map
            sseq
            ~f:(fun l' -> l@l')
            ~size_diff:(List.length l))
    in
    let concat_directory =
      Seq.concat_map
        sseq_seq
      ~f:(fun sseq -> SSeq.to_seq sseq) in
    let () = print_string "print result\n" in
    let () = Seq.iter
           concat_directory
           ~f:(fun l -> print_list l; print_newline ())
    in
    ()    

  let f () =
    print_string "\nTEST SortedSequence:\n";
    (print_string "test concat--------------------------------------------------\n");
    test_concat ();
    (print_string "test concat2--------------------------------------------------\n");
    test_concat2 ()
    
end


    
  
                         
let _ =
  let () = TestPolynomial.f () in
  let () =  TestSolveEquality.f () in
  (* let () =  TestSeq.f () in *)
  (* let () = TestSSeq.f () in *)
  ()
