module Main 
import Data.Vect
import Control.Monad.State

interface Add a where
  add : a -> a -> a
interface Mult a where
  mult : a -> a -> a

Add Double where
  add = (+)
Mult Double where
  mult = (*)

data Gate : Type -> Type -> Type where
  Fixed : Show a => a -> Gate a s
  Parameter : Show a => (s -> a) -> (s -> a -> s) -> Gate a s
  Vect : Show a => Vect (S n) (Gate a s) -> Gate (Vect (S n) a) s
  (+) : (Show a, Add a) => Gate a s -> Gate a s -> Gate a s
  (.) : (Add a, Mult a, Show a) => Gate (Vect (S n) a) s -> Gate (Vect (S n) a) s -> Gate a s

interface Show a => IEvaluated a where
  val : a -> a

Show (Gate a s) where
  show (Fixed x) = show x
  show (Parameter  _ _) = "p"  
  show (a + b) = show a ++ " + " ++ (show b)
  show (a . b) = show a ++ " . " ++ (show b)
  show (Vect x) = "[ " ++ (show (map show x)) ++ " ]" 

data Evaluated : Type -> Type -> Type where
  EvaluatedFixed : Show a => a -> Evaluated a s
  EvaluatedParameter : Show a => (s -> a) -> (s -> a -> s) -> Evaluated a s
  EvaluatedVect : Show a => Vect (S n) (Evaluated a s) -> Vect (S n) a -> Evaluated (Vect (S n) a) s
  EvaluatedAdd : (Show a, Add a) => Evaluated a s -> Evaluated a s -> a ->  Evaluated a s
  EvaluatedDot : (Add a, Mult a, Show a) => Evaluated (Vect (S n1) a) s -> Evaluated (Vect (S n1) a) s -> a -> Evaluated a s

Show (Evaluated a s) where
  show (EvaluatedFixed x) = show x
  show (EvaluatedParameter _ _)  = "p" 
  show (EvaluatedVect x y) = "([ " ++ (show (map show x)) ++ " ] = " ++ (show y) ++ " )"
  show (EvaluatedAdd x y z) = "( " ++  (show x) ++ " + " ++ (show y) ++ " = " ++ (show z) ++ " )"
  show (EvaluatedDot x y z) = "( " ++  (show x) ++ " . " ++ (show y) ++ " = " ++ (show z) ++ " )"

value : MonadState b m => Evaluated a b -> m a 
value (EvaluatedFixed x) = pure x
value (EvaluatedParameter get _) = gets get
value (EvaluatedVect _ ys) = pure ys
value (EvaluatedAdd _ _ z) = pure z 
value (EvaluatedDot _ _ w) = pure w

record Parameters where
  constructor MkParameters
  p1 : Double

Show Parameters where
  show (MkParameters p)  = "{Paramerters: p=" ++ show p ++ " }" 

s1 : Parameters -> Double -> Parameters
s1 s x = record {p1 = x} s

aGate : Gate Double Parameters
aGate =  (Vect [Fixed 2, (Parameter p1 s1) + (Fixed 1)]) . (Vect [Fixed 4, Fixed 5])

dotProduct : (Add a, Mult a) => Vect (S n) a -> Vect (S n) a -> a
dotProduct x y = foldl1 add $ zipWith mult x y

forwardPass: MonadState b m => Gate a b -> m (Evaluated a b)
forwardPass (Fixed x) = pure $ EvaluatedFixed x
forwardPass (Parameter get set) = pure $ EvaluatedParameter get set
forwardPass (Vect xs) = do
  children <- traverse forwardPass xs
  v <- traverse value children
  pure $ EvaluatedVect children v
forwardPass (x + y) = do
  evaluatedX <- forwardPass x
  vx <- value evaluatedX
  evaluatedY <- forwardPass y
  vy <- value evaluatedY
  pure $ EvaluatedAdd evaluatedX evaluatedY $ add vx vy
forwardPass (x . y) = do
  evaluatedX <- forwardPass x
  vx <- value evaluatedX
  evaluatedY <- forwardPass y
  vy <- value evaluatedY
  pure $ EvaluatedDot evaluatedX evaluatedY $ dotProduct vx vy 

run : MonadState Int m => Int -> m ()
run x = modify (+x)
  

main : IO ()
main = do
  putStrLn $ show aGate
  putStrLn "->"
  putStrLn $ show $ runState (forwardPass aGate) (MkParameters 0.4)

evaluated : Evaluated Double Parameters
evaluated = EvaluatedAdd (EvaluatedFixed 1) (EvaluatedFixed 2) 3 

x : Evaluated (Vect 2 Double) Parameters
x = EvaluatedVect [EvaluatedFixed 1, EvaluatedFixed 2] [1,2]

y : Evaluated (Vect 2 Double) Parameters
y = EvaluatedVect [EvaluatedAdd (EvaluatedParameter p1 s1) (EvaluatedFixed 0) 2, EvaluatedFixed 2] [2, 2]

anotherEvaluated : Evaluated Double Parameters
anotherEvaluated = EvaluatedDot x y 6

input1 : Gate Double Parameters
input1 = Fixed 1

input2 : Gate Double Parameters
input2 = Fixed 2

input3 : Gate Double Parameters
input3 = Fixed 3

sum : Gate Double Parameters
sum = input1 + (input2 + input3)


v : Gate (Vect 2 Double) Parameters
v = Vect [Fixed 1, Fixed 2]

dot : Gate Double Parameters
dot = Vect [Fixed 1, Fixed 2, Fixed 3] . Vect [Fixed 2, Parameter p1 s1, Fixed 4] 

--aGate : Gate 2 1
--aGate = 1 >:: 2 >:: 3 ::> Nil

--Show (Gate x y)  where
--    show x = let (inputs, outputs) = counts x in  (show inputs) ++ ">::>" ++ (show outputs)

--main : IO ()
--main = putStrLn $ show aGate 
