data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

total
loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)

-- note, is not total.
runForever : InfIO -> IO ()
runForever (Do action cont) = do
  res <- action
  runForever (cont res)

-- executing infinite processes as total functions

-- run, but giving it a max number of iterations (via a nested structure, Fuel).
data Fuel = Dry | More Fuel

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

total
run : Fuel -> InfIO -> IO ()
run (More fuel) (Do c f) = do
  res <- c
  run fuel (f res)
run Dry y = putStrLn "Out of fuel!"

-- Generating infinite structures via Lazy types

