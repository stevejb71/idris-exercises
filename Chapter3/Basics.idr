import Data.Vect

total allLengths : Vect len String -> Vect len Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

insert : Ord elem => (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem
insert x [] = [x]
insert x (y :: xs) = if x < y then x :: y :: xs else y :: x :: xs

total insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) = let xsSorted = insSort xs in (insert x xsSorted)

total   my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = 1 + my_length xs

total my_append : (x : a) -> (xs : List a) -> List a
my_append x [] = [x]
my_append x (y :: xs) = y :: my_append  x xs

total my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = my_append x (my_reverse xs)

total my_lmap : (a -> b) -> List a -> List b
my_lmap f [] = []
my_lmap f (x :: xs) = f x :: my_lmap f xs

total my_vmap : (a -> b) -> Vect n a -> Vect n b
my_vmap f [] = []
my_vmap f (x :: xs) = f x :: my_vmap f xs
