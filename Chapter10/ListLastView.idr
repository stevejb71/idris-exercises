-- ListLast, a view of a list
data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : Show a => (input : List a) -> (form : ListLast input) -> String
describeHelper [] Empty = "empty list"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "non-empty: initial is " ++ (show xs)

-- covering function of the view ListLast - shows view-like pattern matching
total listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = 
  case listLast xs of
    Empty => NonEmpty [] x
    NonEmpty ys y => NonEmpty (x :: ys) y

describeListEnd1 : Show a => (xs : List a) -> String
describeListEnd1 xs = describeHelper xs (listLast xs)

--- using the with construct - no need for helper

describeListEnd : List Int -> String
describeListEnd input with (listLast input)
  describeListEnd [] | Empty = "empty list"
  describeListEnd (xs ++ [x]) | (NonEmpty xs x) = "non-empty: initial is " ++ (show xs)


-- note, cannot be proven total by Idris, as it cannot prove xs is smaller
-- the xs ++ [x], because ++ is not a data constructor of List.
-- Also, inefficient, O(n^2)
myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys
