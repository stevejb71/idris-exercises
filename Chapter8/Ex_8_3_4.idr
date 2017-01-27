data Vector : (len : Nat) -> (elem : Type) -> Type where
  Empty : Vector 0 xs
  Cons : (x : elem) -> (xs : Vector len elem) -> Vector (S len) elem

eg : Vector 2 Integer
eg = Cons 1 (Cons 2 Empty)

total headUnequal : DecEq a => 
  {xs : Vector n a} -> 
  {ys : Vector n a} -> 
  (contra: (x = y) -> Void) -> 
  ((Cons x xs) = (Cons y ys)) -> Void 
headUnequal contra Refl = contra Refl  

total tailUnequal : DecEq a => 
  {xs : Vector n a} ->
  {ys : Vector n a} -> 
  (contra: (xs = ys) -> Void) -> 
  ((Cons x xs) = (Cons y ys) -> Void) 
tailUnequal contra Refl = contra Refl   

total DecEq a => DecEq (Vector n a) where         
  decEq Empty Empty = Yes Refl
  decEq (Cons x xs) (Cons y ys) = 
    case decEq x y of
      Yes Refl => 
        case decEq xs ys of 
          Yes Refl => Yes Refl
          No contra => No (tailUnequal contra)
      No contra => 
        No (headUnequal contra)