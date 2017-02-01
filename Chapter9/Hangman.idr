import Data.Vect

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guesses_remaining letters

data Finished : Type where 
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won : (game : WordState (S letters) 0) -> Finished

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]

total isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No emptyInvalid
  where emptyInvalid : ValidInput [] -> Void
        emptyInvalid (Letter _) impossible
isValidInput [x] = Yes (Letter x)
isValidInput (x :: y :: xs) = No moreThan1CharInvalid  
  where moreThan1CharInvalid : ValidInput (x :: y :: xs) -> Void
        moreThan1CharInvalid (Letter _) impossible

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput $ unpack s

readGuess : IO (x ** ValidInput x)
readGuess = do
  putStr "Guess: "
  x <- getLine
  case isValidString (toUpper x) of
    Yes prf => pure (_ ** prf)
    No _ => do
      putStrLn "Only 1 letter please"
      readGuess

total removeElem :
  (value : a) ->
  (xs : Vect (S n) a) ->
  (prf : Elem value xs) ->
  Vect n a  
removeElem x (x :: xs) Here = xs
removeElem {n = Z} value ([_]) (There later) = absurd later
removeElem {n = (S k)} value (x :: xs) (There later) = x :: removeElem value xs later

total removeElem_auto :
  (value : a) ->
  (xs : Vect (S n) a) ->
  {auto prf : Elem value xs} ->
  Vect n a  
removeElem_auto value xs {prf} = removeElem value xs prf

processGuess : (letter : Char) 
  -> WordState (S guesses) (S letters) 
  -> Either (WordState guesses (S letters)) (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) = 
  case isElem letter missing of
    Yes prf => Right (MkWordState word (removeElem_auto letter missing))
    No contra => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st = do
  (_ ** Letter letter) <- readGuess
  case processGuess letter st of
    Left l => do
      putStrLn "Wrong!"
      case guesses of
        Z => pure (Lost l)
        S k => game l
    Right r => do
      putStrLn "Right!"
      case letters of
        Z => pure (Won r)
        S k => game r

main : IO ()
main = do
  result <- game {guesses=2} (MkWordState "Test" ['T','E','S'])
  putStrLn $ case result of
    Lost (MkWordState word _) => ("You lost, word was " ++ word)
    Won game => "You win!"