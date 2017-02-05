import Data.Vect
import Data.Vect.Views

mergeSort : Ord a => Vect n a -> Vect n a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (xs ++ ys) | (SplitRecPair lrec rrec) = 
    merge (mergeSort xs | lrec) (mergeSort ys | rrec)