data Vect : Nat -> Type -> Type where
  Empty : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

-- FAIL - m == len does not guarantee that m and len are equal
-- exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
-- exactLength {m} len input = 
--   case m == len of
--     False => Nothing
--     True => Just input

data EqNat : (n : Nat) -> (m : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : (k : Nat) -> (j: Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS k k (Same k) = Same (S k)

-- Version not using inbuilt = type
-- checkEqNat : (n1 : Nat) -> (n2 : Nat) -> Maybe (EqNat n1 n2)
-- checkEqNat Z Z = Just $ Same Z
-- checkEqNat (S m1) (S m2) = 
--   case checkEqNat m1 m2 of
--     Nothing => Nothing
--     Just eq => Just $ (sameS _ _ eq)
-- checkEqNat _ _ = Nothing

checkEqNat : (n1 : Nat) -> (n2 : Nat) -> Maybe (n1 = n2)
checkEqNat Z Z = Just Refl
checkEqNat (S j) (S k) = 
  case checkEqNat j k of
    Nothing => Nothing
    Just x => Just $ cong x   -- also Just Refl => Just Refl
checkEqNat _ _ = Nothing

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = 
  case checkEqNat m len of
    Nothing => Nothing
    Just Refl => Just input