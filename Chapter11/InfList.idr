data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

total
countFrom : Integer -> InfList Integer
countFrom n = n :: countFrom (n+1) -- Delay is inserted by the compiler.

total
infZip : InfList a -> List b -> List (a, b)
infZip _ [] = []
infZip (x :: xs) (y :: ys) = (x, y) :: infZip xs ys 

total
label : List a -> List (Integer, a)
label = infZip (countFrom 0) 

total
getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z _ = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs
