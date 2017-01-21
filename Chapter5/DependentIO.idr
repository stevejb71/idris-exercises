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
               case exactLength len1 vec2 of
                  Nothing => putStrLn "Different lengths"
                  Just vec2' => printLn $ zip vec1 vec2'
