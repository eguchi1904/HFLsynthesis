open Hfl

let horn (`Horn (cs,c)) =
  match c with
  | `Base (BaseLogic.Bool true) -> true
  | _ ->
     let z3_cs = List.map UseZ3.clause_to_z3_expr cs |> List.map fst in
     let z3_c = UseZ3.clause_to_z3_expr c |> fst in
     let z3_expr = UseZ3.mk_horn z3_cs z3_c in
      UseZ3.is_valid z3_expr

     

