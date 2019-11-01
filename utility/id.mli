type t = private int

val valueVar_id:t
  
val genid: string -> t

val genid_from_id: t -> t

val genid_const: string -> t

val to_int: t -> int
  
val to_string: t -> string

val to_string_readable: t -> string

val of_string_symbol: string -> t

(* val valueVar_id: t *)

  
   
