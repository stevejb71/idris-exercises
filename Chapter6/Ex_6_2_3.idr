import Data.Vect

Matrix : (n: Nat) -> (m: Nat) -> Type
Matrix n m = Vect n (Vect m Double)

testMatrix : Matrix 2 3
testMatrix = [[0,0,0],[0,0,0]]

TupleVect : Nat -> Type -> Type
TupleVect Z _ = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

test : TupleVect 4 Nat
test = (1,2,3,4,())
