data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

total takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z _ = Exact []
takeN (S k) [] = Fewer
takeN (S k) (y :: ys) =
  case takeN k ys of
    Fewer => Fewer
    Exact k_xs => Exact (y :: k_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (div (length xs) 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)
