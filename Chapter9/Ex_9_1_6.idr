data Last : List a -> a -> Type where
  LastOne  : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1, 2, 3] 3
last123 = LastCons (LastCons LastOne)

lastOnEmpty : Last [] value -> Void
lastOnEmpty LastOne impossible
lastOnEmpty (LastCons _) impossible

rhs : (contra2 : Last xs value -> Void) -> (contra1 : (xs = [value]) -> Void) -> Dec (Last (x :: xs) value)
rhs contra2 contra1 = ?rhs_rhs_2

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No lastOnEmpty
isLast (x :: xs) value = case decEq xs [value] of
                              Yes Refl => Yes (LastCons LastOne)
                              No contra1 => case isLast xs value of
                                                Yes prf => Yes (LastCons prf)
                                                No contra2 => rhs contra2 contra1
