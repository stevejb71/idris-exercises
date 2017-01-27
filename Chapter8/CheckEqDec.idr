zeroNotSuc : (0 = S k) -> Void
zeroNotSuc Refl impossible

sucNotZero : (S k = 0) -> Void
sucNotZero Refl impossible

noRec : (contra : (j = k) -> Void) -> (S j = S k) -> Void
noRec contra Refl = contra Refl

checkEqNat : (n1 : Nat) -> (n2 : Nat) -> Dec (n1 = n2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSuc
checkEqNat (S k) Z = No sucNotZero
checkEqNat (S j) (S k) = 
  case checkEqNat j k of
    No contra => No (noRec contra)
    Yes prf => Yes (cong prf)
