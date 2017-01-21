totalLen : List String -> Nat
totalLen xs = foldr (\s, acc => length s + acc) 0 xs

data Tree a = 
  Empty
| Node (Tree a) a (Tree a)

Foldable Tree where    
  foldr func acc Empty = acc
  foldr func acc (Node l e r) = 
    let lf = foldr func acc l
        rf = foldr func lf r
    in func e rf
