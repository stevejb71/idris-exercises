data SplitList : List a -> Type where 
  SplitNil : SplitList []
  SplitOne : SplitList [x]  -- x is an implicit argument
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total splitList : (input : List a) -> SplitList input 
splitList input = helper input input
  where
    total helper : List a -> (input : List a) -> SplitList input
    helper x [] = SplitNil
    helper _ [x] = SplitOne      
    helper (_ :: _ :: counter) (item :: items) = 
      case helper counter items of
         SplitNil => SplitOne
         SplitOne {x} => SplitPair [item] [x]
         SplitPair lefts rights => SplitPair (item :: lefts) rights
    helper _ items = SplitPair [] items     

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) = 
    merge (mergeSort lefts) (mergeSort rights)
