
let is_divisor n c =
  (n = 0)
  ||(is_divisor (n - c) c)

let cd n m c =
  (is_divisor n c)&&(is_divisor m c)

let gcd_i n m i c =
  (cd i n && cd i m && c = i)
  ||(gcd_i n m (i-1) c)

let[@spec gcd] gcd n m c = gcd_i n m m c
