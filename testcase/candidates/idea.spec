

is_prefix l sub =
(l = [] && sub = [])
or(l = x::xs && sub = s::ss &&
     x = s && is_prefix xs ss)


is_sufix l sub

is_substring l sub

rev l rev = 


split_
[....;a;...;] -> [....;a], [....]

[a,b,a,b,..] -> [a;a;a;a],[b,b,b,...]


reshape
補助関数は必要だろうな。
[a11, a12,..,a21,....,anm] n m ->
[[a11,....a1m],
 [a21,....   ],
 ,,,]

データ構造なし出会いかな。

MULT a b r =
 (b = 0 && r = 0)
 && (MULT  a  (b-1) (r-b))

割り算, しょうとあまりを出す
(a:int) (b:int) (q:int,r:int)=
MULT (a, q, b -r)

最大公約数
はだいぶ実装＝になりそうだ

GCD(n, m, g) =
(n = m && g = n)
or (n > m && GCD (n-m, m, g))
or (n < m && GCD (n, m-n, g))


例えばこういうのを溶けるかは純粋に展開では難しいか。mu2chcがといてくれれば良い。

gcd n m =
if n = m then n
   else if n > m then
    let q,r = del n m in
     gcd r m


まずrには
MULT (n, q, m-r)
とかでいけるのかな。

そういう意味で素因数分解とかできてもおかしくはないか
	   
- メモかfibonachとか　（まあどれくらい意味があるかと言われると...)

fibo_memo l n -> fibo_memo v n+1

- 列挙系、
順列の列挙。
nPmを定義して、
uniqueなリストリトそを返す

- lがユニークだったらそれを返さないといけないので。
  l:LIst -> {UniqList List | len v = nPm && elm v = elm l}


