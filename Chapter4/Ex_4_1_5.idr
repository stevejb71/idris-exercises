data Tree a = Empty
            | Node (Tree a) a (Tree a)
%name Tree tree, tree1

insert : Ord a => a -> Tree a -> Tree a
insert x Empty = Node Empty x Empty
insert x n@(Node lhs y rhs)
  = case compare x y of
      LT => Node (insert x lhs) y rhs
      EQ => n
      GT => Node lhs y (insert x rhs)

listToTree : Ord a => List a -> Tree a
listToTree = foldr insert Empty

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node lhs x rhs) = treeToList lhs ++ (x :: treeToList rhs)

----

data Expr = Value Int
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr

evaluate : Expr -> Int
evaluate (Value x) = x
evaluate (Add x y) = evaluate x + evaluate y
evaluate (Sub x y) = evaluate x - evaluate y
evaluate (Mul x y) = evaluate x * evaluate y

----

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe x y = max <$> x <*> y
