module DataStore

import Data.Vect

infix 5 .+.

public export
data Schema = SString 
            | SInt
            | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (value : SchemaType schema) -> (store : DataStore schema) -> DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

testStore : DataStore (SString .+. SInt)
testStore = addToStore ("abc",3) $ addToStore ("cdef", 4) $ empty

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewHelp : (items : Vect size (SchemaType schema)) -> StoreView (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (x :: xs) = SAdd (storeViewHelp xs)

export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelp items

-- client

showItems : DataStore schema -> List (SchemaType schema)
showItems input with (storeView input)
  showItems input | SNil = []
  showItems (addToStore value store) | (SAdd rec) = 
    value :: showItems store | rec

filterKeys : (test : SchemaType val_schema -> Bool) -> DataStore (SString .+. val_schema) -> List String
filterKeys test input with (storeView input)
  filterKeys _ _ | SNil = []
  filterKeys test (addToStore (key, value) store) | (SAdd rec) = 
    (if test value then key :: filterKeys test store else filterKeys test store) | rec

-- Ex 10.3.4

getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues input with (storeView input)
  getValues input | SNil = []
  getValues (addToStore value store) | (SAdd rec) = ?input_rhs_2
