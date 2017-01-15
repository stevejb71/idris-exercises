module Main

import Data.Vect

infix 5 .+.

data Schema = SString 
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema: Schema
  size : Nat
  items : Vect size (SchemaType schema)

total addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size store) newitem = MkData schema _ (addToData store)
  where addToData : Vect oldsize (SchemaType schema) -> Vect (S oldsize) (SchemaType schema)
        addToData [] = [newitem]
        addToData (item :: items) = item :: addToData items

data Command : Schema -> Type where 
  Add : SchemaType schema -> Command schema 
  Get : Integer -> Command schema 
  Size : Command schema
  Search : String -> Command schema 
  Quit : Command schema

total parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" item = Just (Add (?parseBySchema item))
parseCommand schema "get" index = if all isDigit (unpack index)
                           then Just (Get $ cast index)
                           else Nothing
parseCommand schema "size" "" = Just Size
parseCommand schema "quit" "" = Just Quit
parseCommand schema "search" substr = Just (Search substr)
parseCommand _ _ _ = Nothing

total parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                       (cmd, args) => parseCommand schema cmd (ltrim args)

total getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store@(MkData schema size items) =
  case integerToFin pos size of
    Nothing => Just ("Out of range\n", store)
    Just id => Just (?display (index id items) ++ "\n", store)

searchEntry : (sub : String) -> (ds : DataStore) -> Maybe (String, DataStore)
searchEntry sub ds = Nothing
  -- let found = snd $ Data.Vect.filter (?isInfixOf sub) $ items ds
  --     found_str = (concat $ toList $ Data.Vect.intersperse "," $ map show found) ++ "\n"
  --     in Just (found_str, ds)

total processInput : DataStore -> String -> Maybe (String, DataStore)
processInput ds@(MkData schema _ items) cmd = case parse schema cmd of
                        Nothing => Just ("Invalid command\n", ds)
                        Just (Add item) => Just ("ID " ++ show (size ds) ++ "\n", addToStore ds (?convert item))
                        Just (Get index) => getEntry index ds
                        Just Size => Just ("SIZE " ++ show (size ds) ++ "\n", ds)
                        Just (Search substr) => searchEntry substr ds
                        Just Quit => Nothing

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
