import Data.Vect

append_xs : Vect (S (m + len)) elem -> Vect (plus m (S len)) elem
append_xs {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

-- Note, works straight off with n+m rather than m+n
append : Vect n elem -> Vect m elem -> Vect (m+n) elem 
append {m} [] ys = rewrite plusZeroRightNeutral m in ys
append (x :: xs) ys = append_xs (x :: append xs ys)
