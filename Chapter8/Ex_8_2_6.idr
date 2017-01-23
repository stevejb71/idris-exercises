import Data.Vect

%default total

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite (plusZeroRightNeutral m) in Refl
myPlusCommutes (S k) m = 
  rewrite (myPlusCommutes k m) 
  in rewrite (plusSuccRightSucc m k) in Refl

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n+m) a
        reverse' {n} acc [] = rewrite (plusZeroRightNeutral n) in acc
        reverse' {n} {m = S len} acc (x :: xs) = 
          rewrite (sym $ plusSuccRightSucc n len) in (reverse' (x::acc) xs)