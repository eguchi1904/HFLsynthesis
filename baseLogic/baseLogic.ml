include Formula
      
let is_valid (t:t) =
  let z3_exp, _ = UseZ3.convert t in
  UseZ3.is_valid z3_exp


let to_z3_expr t = UseZ3.convert t
