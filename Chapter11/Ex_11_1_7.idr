everyOther : Stream ty -> Stream ty
everyOther = go False
  where go : Bool -> Stream ty -> Stream ty
        go False (_ :: xs) = go True xs
        go True (x :: xs) = x :: go False xs

-- InfList + functor

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

total
getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z _ = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

total
countFrom : Integer -> InfList Integer
countFrom n = n :: countFrom (n+1)

implementation Functor InfList where
    map f (x :: xs) = f x :: map f xs  

-- END: InfList + functor

-- Ex 3

data Face = Head | Tail

getFace : Int -> Face
getFace x = if (x `mod` 2) == 0 then Head else Tail

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips count xs = take count (map getFace xs)

-- Ex 4

approxSquareRoots : (number : Double) -> (approx : Double) -> Stream Double
approxSquareRoots number approx = approx :: approxSquareRoots number next
  where next = (approx + (number / approx)) / 2

-- Ex 5

squareRootBound : (max : Nat) -> (number : Double) -> (bound : Double) -> (approxs: Stream Double) -> Double
squareRootBound Z _ _ (value :: _) = value
squareRootBound (S k) number bound (x :: xs) = 
  if abs (x * x - number) < bound then x else squareRootBound k number bound xs

squareRoot : (number : Double) -> Double
squareRoot number = squareRootBound 100 number 0.00000001 (approxSquareRoots number number)