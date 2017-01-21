occurrences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurrences item [] = 0
occurrences item (x :: xs) = (if x == item then 1 else 0) + (occurrences item xs)

data Matter = Solid | Liquid | Gas

Eq Matter where
    (==) Solid Solid = True
    (==) Liquid Liquid = True
    (==) Gas Gas = True
    (==) _ _ = False

----

data Expr num = 
        Val num
      | Add (Expr num) (Expr num) 
      | Sub (Expr num) (Expr num) 
      | Mul (Expr num) (Expr num) 
      | Div (Expr num) (Expr num) 
      | Abs (Expr num)

eval : (Neg num, Integral num) => Expr num -> num 
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs $ eval x

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub
  abs = Abs

-- Ex 7.2.4

br : String -> String
br s = "(" ++ s ++ ")"

Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = br $ show x ++ " + " ++ show y
  show (Sub x y) = br $ show x ++ " - " ++ show y
  show (Mul x y) = br $ show x ++ " * " ++ show y
  show (Div x y) = br $ show x ++ " div " ++ show y
  show (Abs x) = "abs(" ++ show x ++ ")"

Eq ty => Eq (Expr ty) where    
