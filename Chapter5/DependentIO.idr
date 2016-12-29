import Data.Vect

readVect : IO (len ** Vect len String)
readVect = do x <- getLine
              if x == ""
              then pure (_ ** [])
              else do (_ ** xs) <- readVect
                      pure (_ ** x :: xs)

zipInputs : IO ()
zipInputs = do putStrLn "Enter first (blank line to end):"
               (len1 ** vec1) <- readVect
               putStrLn "Enter second (blank line to end):"
               (len2 ** vec2) <- readVect
               if len1 == len2 then ?zipInputs_rhs1 else ?zipInputs_rhs2
