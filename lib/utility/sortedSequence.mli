module type SORTEDSEQUENCE = sig
  type 'a t

  val empty: 'a t
    
  val to_seq: 'a t -> 'a Base.Sequence.t

  val append_sequence: 'a Base.Sequence.t -> size:int -> 'a t -> 'a t

  val append: 'a t -> 'a t -> 'a t

  val map: 'a t -> f:('a -> 'b) -> size_diff:int -> 'b t

  (* ここで適切に遅延されることが大事 *)
  val concat: 'a t Base.Sequence.t -> min_size:int -> 'a t

  val concat2: 'a t t -> min_size:int -> 'a t    
    
  val single_size: 'a t -> 'a Base.Sequence.t option
    
end

val generator: size_max:int -> (module SORTEDSEQUENCE)
  
