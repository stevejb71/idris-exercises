import Data.Vect

removeElem : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
removeElem value (x :: xs) = 
  case decEq value x of
    Yes _ => xs
    No _ => ?no
