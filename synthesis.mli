module type SYNTHESIZER = sig
  
  val  f: Hfl.Equations.t -> PathEnv.t -> Id.t -> Hfl.sort -> spec:Hfl.fhorn -> Program.t
     
end

val generator: DataType.Env.t -> Qualifier.t list -> int -> (module SYNTHESIZER)

 
