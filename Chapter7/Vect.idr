data Vect : (len : Nat) -> (elem : Type) -> Type where
  Empty : Vect 0 xs
  (::) : (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem

%name Vect xs,ys,zs,ws  

Eq ty => Eq (Vect n ty) where
  (==) Empty Empty = True
  (==) (x :: xs) (y :: ys) = x == y && xs == ys

Foldable (Vect n) where
  foldr f init Empty = init
  foldr f init (x :: xs) = f x (foldr f init xs)
