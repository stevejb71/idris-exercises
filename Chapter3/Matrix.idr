import Data.Vect

addMatrix : Num numType => Vect rows (Vect cols numType) -> Vect rows (Vect cols numType) -> Vect rows (Vect cols numType)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeHelper : (x : Vect n elem) -> (xsTrans : Vect n (Vect k elem)) -> Vect n (Vect (S k) elem)
transposeHelper = zipWith (::)

transposeMatrix : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMatrix [] = createEmpties
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in (transposeHelper x xsTrans)

multHelper : Num numType => (x : Vect m numType) -> (ys : Vect p (Vect m numType)) -> Vect p numType
multHelper x [] = []
multHelper x (y :: ys) = sum (zipWith (*) x y) :: multHelper x ys

multMatrix : Num numType => Vect n (Vect m numType) -> Vect m (Vect p numType) -> Vect n (Vect p numType)
multMatrix xs = multMatrixT xs . transposeMatrix
  where multMatrixT : Num numType => Vect n (Vect m numType) -> Vect p (Vect m numType) -> Vect n (Vect p numType)
        multMatrixT [] ys = []
        multMatrixT (x :: xs) ys = multHelper x ys :: multMatrixT xs ys
