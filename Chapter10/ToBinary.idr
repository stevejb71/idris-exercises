import Data.Nat.Views

toBinary : Nat -> String
toBinary n with (halfRec n)
  toBinary Z | HalfRecZ = "0"
  toBinary (x + x) | (HalfRecEven rec) = (if x == 0 then "" else toBinary x) ++ "0"
  toBinary (S (x + x)) | (HalfRecOdd rec) = (if x == 0 then "" else toBinary x) ++ "1"
