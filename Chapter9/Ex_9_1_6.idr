import Data.List

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notThere : Elem value xs -> Void) -> (notHere : (value = x) -> Void) -> Elem value (x :: xs) -> Void
notInTail notThere notHere Here = notHere Refl
notInTail notThere notHere (There later) = notThere later

total myIsElem : DecEq a => (value : a) -> (xs : List a) -> Dec (Elem value xs)
myIsElem value [] = No notInNil
myIsElem value (x :: xs) = 
  case decEq value x of
    Yes Refl => Yes Here
    No notHere => 
      case myIsElem value xs of
        Yes prf => Yes (There prf)
        No notThere => No (notInTail notThere notHere)

--- Last

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

nilHasNoLast : Last [] value -> Void
nilHasNoLast LastOne impossible
nilHasNoLast (LastCons _) impossible

total no : (notFound : Last (x :: xs) value -> Void) -> Last (_ :: x :: xs) value -> Void
no notFound (LastCons prf) = notFound prf

total lastNotEq : (con : (x = value) -> Void) -> Last [x] value -> Void
lastNotEq con LastOne = con Refl
lastNotEq _ (LastCons LastOne) impossible
lastNotEq _ (LastCons (LastCons _)) impossible

total isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] _ = No nilHasNoLast
isLast [x] value =
  case decEq x value of
    Yes Refl => Yes LastOne
    No con => No (lastNotEq con)
isLast (_ :: x :: xs) value =
  case isLast (x :: xs) value of
    No notFound => No (no notFound)
    Yes LastOne => Yes (LastCons LastOne)
    Yes (LastCons prf) => Yes (LastCons (LastCons prf)) 
