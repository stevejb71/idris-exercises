import Data.List.Views

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix input1 input2 with (snocList input1)
  equalSuffix [] _ | Empty = []
  equalSuffix (xs ++ [x]) input2 | (Snoc rec1) with (snocList input2)
    equalSuffix (xs ++ [x]) [] | (Snoc rec1) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc rec1) | (Snoc rec2) = 
      if x == y
      then (equalSuffix xs ys) ++ [x] | rec1 | rec2
      else []
