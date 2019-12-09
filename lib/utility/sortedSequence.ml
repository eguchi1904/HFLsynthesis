module Seq = Base.Sequence
           
module type SORTEDSEQUENCE = sig
  type 'a t

  val empty: 'a t
    
  val to_seq: 'a t -> 'a Seq.t

  val append_sequence: 'a Seq.t -> size:int -> 'a t -> 'a t

  val append: 'a t -> 'a t -> 'a t

  val map: 'a t -> f:('a -> 'b) -> size_diff:int -> 'b t

  val concat: 'a t Seq.t -> min_size:int -> 'a t

  val single_size: 'a t -> 'a Seq.t option
  
     
end

                           
let generator ~size_max =
  (module struct
  
  type 'a t =  'a Seq.t Seq.t
  (* [seq1; seq2;....]  
     (seq1's elm size) +1 = (seq2's elm size)
     (seq2's elm size) +1 = (seq3's elm size)
     ...

   *)

             

  let empty =
    Seq.unfold
      ~init:0
      ~f:(fun i ->
          if i <= size_max then
            Some (Seq.empty, i+1)
          else
            None)


  let to_seq t =
    Seq.concat t
    
             
  let rec append t1 t2 =
    Seq.unfold
      ~init:(t1, t2)
      ~f:(fun (t1, t2) ->
        match (Seq.next t1), (Seq.next t2) with
        |Some (hd1, t1'), Some (hd2 ,t2') ->
          Some ((Seq.append hd1 hd2), (t1', t2'))
        |None, Some (hd2, t2') ->
          Some (hd2, (Seq.empty, t2'))
        |Some (hd1, t1'), None ->
          Some (hd1, (t1', Seq.empty))
        |None, None ->
          None
      )
  

  let rec shift_right n t =
    if n <= 0 then t
    else
      Seq.shift_right
        (shift_right (n-1) t) (Seq.empty) 


  let rec append_sequence seq ~size t =
    if size < 1 then invalid_arg "append_sequence: not impl"
    else
      (* tの最初の要素に *)
      Seq.folding_map
        t
        ~init:1
        ~f:(fun i t_elm ->
          if size = i then
            (i+1, Seq.append seq t_elm)
          else
            (i+1, t_elm))
  |> Seq.memoize

 
  (* 頑張ろうな *)
  let concat (t_seq:'a t Seq.t) ~min_size =
    Seq.unfold
      ~init:(1, t_seq)
      ~f:(fun (i, t_seq) ->
        if i > size_max then None
        else
          (* let () = (Printf.printf "in concat: size %d\n" i) in *)
          let heads_tl_seq = 
            Seq.concat_map
              t_seq
              ~f:(fun t ->
                match Seq.next t with
                |None -> Seq.empty |Some (head_seq, remain) ->
                                     Seq.singleton (head_seq,remain))
          in
          let heads_seq, tls_seq =
            (Seq.map heads_tl_seq ~f:fst), (Seq.map heads_tl_seq ~f:snd)
          in
          if i < min_size then  (* head seqを消費しない。 *)
            Some (Seq.empty, (i+1, tls_seq))
          else
            Some (Seq.concat heads_seq, ((i+1), tls_seq)))

    |> Seq.memoize    

                    
  let map t ~f ~size_diff:added_size =
    assert (added_size >= 0);
    (* let () = (Printf.printf "in sseq map:\n") in     *)
    let t' = Seq.map
               ~f:(fun seq -> Seq.map ~f:f seq)
               t
    in
    shift_right added_size t' |> Seq.memoize

  let single_size t = Seq.hd t

    end: SORTEDSEQUENCE)
  
  
  
                  
