data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])
%name SnocList snoc, snoc1

snocListHelp : (snoc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input} snoc (x :: xs) = 
  rewrite appendAssociative input [x] xs in 
    snocListHelp (Snoc snoc) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

total myReverseHelper : (input : List a) -> SnocList input -> List a
myReverseHelper [] Empty = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

total myReverse : List a -> List a
myReverse xs = myReverseHelper xs (snocList xs)

total myReverse2 : List a -> List a
myReverse2 input with (snocList input)
  myReverse2 [] | Empty = []
  myReverse2 (xs ++ [x]) | (Snoc rec) = x :: myReverse2 xs | rec
