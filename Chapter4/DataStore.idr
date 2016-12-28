module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

total size : DataStore -> Nat
size (MkData size _) = size

total items : (store : DataStore) -> Vect (size store) String
items (MkData _ items) = items

total addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) item = MkData _ (items ++ [item])

data Command = Add String | Get Integer | Size | Search String | Quit

total parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" item = Just (Add item)
parseCommand "get" index = if all isDigit (unpack index)
                           then Just (Get $ cast index)
                           else Nothing
parseCommand "size" "" = Just Size
parseCommand "quit" "" = Just Quit
parseCommand "search" substr = Just (Search substr)
parseCommand _ _ = Nothing

total parse : String -> Maybe Command
parse input = case span (/= ' ') input of
                (cmd, args) => parseCommand cmd (ltrim args)

total getEntry : Integer -> DataStore -> Maybe (String, DataStore)
getEntry pos ds@(MkData size items) =
  case integerToFin pos size of
    Nothing => Just ("Out of range\n", ds)
    Just id => Just (index id items ++ "\n", ds)

searchEntry : (sub : String) -> (ds : DataStore) -> Maybe (String, DataStore)
searchEntry sub ds =
  let found = snd $ Data.Vect.filter (isInfixOf sub) $ items ds
      found_str = (concat $ toList $ Data.Vect.intersperse "," $ map show found) ++ "\n"
      in Just (found_str, ds)

total processInput : DataStore -> String -> Maybe (String, DataStore)
processInput ds cmd = case parse cmd of
                        Nothing => Just ("Invalid command\n", ds)
                        Just (Add item) => Just ("ID " ++ show (size ds) ++ "\n", addToStore ds item)
                        Just (Get index) => getEntry index ds
                        Just Size => Just ("SIZE " ++ show (size ds) ++ "\n", ds)
                        Just (Search substr) => searchEntry substr ds
                        Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
