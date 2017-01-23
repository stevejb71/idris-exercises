import Data.Vect

total myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs) = 
  let result = myReverse xs ++ [x] in
      rewrite plusCommutative 1 k in 
  result

total myReverse2 : Vect n elem -> Vect n elem
myReverse2 [] = []
myReverse2 (x :: xs) = 
  reverseProof x xs $ myReverse xs ++ [x]
  where reverseProof : (x : elem) -> (xs : Vect len elem) -> Vect (len + 1) elem -> Vect (S len) elem
        reverseProof {len} x xs result = rewrite plusCommutative 1 len in result