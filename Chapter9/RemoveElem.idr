import Data.Vect

-- removing an element and expecting vector length to decrement 1
-- need proof that the element is in the vector in the fist place
-- otherwise cannot implement ?no case
removeElemX : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
removeElemX value (x :: xs) = 
  case decEq value x of
    Yes _ => xs
    No _ => ?no

-- Usage of Elem with constructors Here and There which can prove
-- that a vector contains an element.
maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

-- removeElem using Elem
total removeElem :
  (value : a) ->
  (xs : Vect (S n) a) ->
  (prf : Elem value xs) ->
  Vect n a  
removeElem x (x :: xs) Here = xs
removeElem {n = Z} value ([_]) (There later) = absurd later
removeElem {n = (S k)} value (x :: xs) (There later) = x :: removeElem value xs later

total removeElem_auto :
  (value : a) ->
  (xs : Vect (S n) a) ->
  {auto prf : Elem value xs} ->
  Vect n a  
removeElem_auto value xs {prf} = removeElem value xs prf