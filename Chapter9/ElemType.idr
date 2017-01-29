import Data.Vect

data MyElem : a -> Vect k a -> Type where
   Here : MyElem x (x :: xs)
   There : (later : MyElem x xs) -> MyElem x (y :: xs)

notInTail : (notHere : (value = x) -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

myIsElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
myIsElem value [] = No notInNil
myIsElem value (x :: xs) =
  case decEq value x of
    Yes Refl => Yes Here
    No notHere => 
      case myIsElem value xs of
        Yes prf => Yes (There prf)
        No notThere => No (notInTail notHere notThere)
