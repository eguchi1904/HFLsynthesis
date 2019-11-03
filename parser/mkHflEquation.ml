open ParseSyntax
open Extensions

let rec g pmap ep t =
  match t with
  |QualifierDef _ :: other |Goal _ :: other
   |DataDef _ :: other |MeasureDef _ :: other |RefinePredicateDef _ :: other ->
    g pmap ep other

  |PredicateDef predicate_def :: other ->
    (* mk_fhornを使うだけか.. *)
    let fhorn = mk_fhorn pmap predicate_def in
    let name = predicate_def.name in
    let fixpoint = predicate_def.fixpoint in
    let () = Hfl.Equations.add ep name fixpoint fhorn in
    g pmap ep other

  |VarSpecDec (var_name, predicate_def) :: other ->
    let fhorn = mk_specification_fhorn var_name pmap predicate_def in
    let fixpoint = predicate_def.fixpoint in
    let () = Hfl.Equations.add ep var_name fixpoint fhorn in
    g pmap ep other

  |[] -> ep

       
let add_constructor data_env ep =
  DataType.Env.fold_datatype
    (fun data (def:DataType.definition) () ->
      List.iter
        (fun (cons:DataType.constructor) ->
          let fhorn = DataType.Env.constructor_specification
                        data_env
                        (`DataS data)
                        cons.name
          in
          Hfl.Equations.add ep cons.name None fhorn)
        def.constructors)
    data_env
    ()
          
      
  


let f (data_env:DataType.Env.t) pmap t =
  let ep = g pmap (Hfl.Equations.make ()) t in
  let () = add_constructor data_env ep in
  ep
  
    
    
   
  
    
    
