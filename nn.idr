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

data Gate : Type -> Type where
  Parameter : Show a => a -> Gate a
  Vect : Show a => Vect (S n) (Gate a) -> Gate (Vect (S n) a)
  (+) : (Show a, Add a) => Gate a  -> Gate a -> Gate a
  (.) : (Add a, Mult a, Show a) => Gate (Vect (S n) a) -> Gate (Vect (S n) a) -> Gate a

interface Show a => IEvaluated a where
  val : a -> a

Show (Gate a) where
  show (Parameter x) = show x
  show (a + b) = show a ++ " + " ++ (show b)
  show (a . b) = show a ++ " . " ++ (show b)
  show (Vect x) = "[ " ++ (show (map show x)) ++ " ]" 

data Evaluated : Type -> Type where
  EvaluatedParameter : Show a => a -> Evaluated a
  EvaluatedVect : Show a => Vect (S n) (Evaluated a) -> Vect (S n) a -> Evaluated (Vect (S n) a)
  EvaluatedAdd : (Show a, Add a) => Evaluated a -> Evaluated a -> a ->  Evaluated a
  EvaluatedDot : (Add a, Mult a, Show a) => Evaluated (Vect (S n1) a) -> Evaluated (Vect (S n1) a) -> a -> Evaluated a

Show (Evaluated a) where
  show (EvaluatedParameter x)  = show x
  show (EvaluatedVect x y) = "([ " ++ (show (map show x)) ++ " ] = " ++ (show y) ++ " )"
  show (EvaluatedAdd x y z) = "( " ++  (show x) ++ " + " ++ (show y) ++ " = " ++ (show z) ++ " )"
  show (EvaluatedDot x y z) = "( " ++  (show x) ++ " . " ++ (show y) ++ " = " ++ (show z) ++ " )"

value : Evaluated a -> a
value (EvaluatedParameter x) = x
value (EvaluatedVect _ ys) = ys
value (EvaluatedAdd _ _ z) = z 
value (EvaluatedDot _ _ w) = w

aGate : Gate Double
aGate =  (Vect [Parameter 2, (Parameter 3) + (Parameter 1)]) . (Vect [Parameter 4, Parameter 5])

dotProduct : (Add a, Mult a) => Vect (S n) a -> Vect (S n) a -> a
dotProduct x y = foldl1 add $ zipWith mult x y

evaluate : Gate a -> Evaluated a
evaluate (Parameter x) = EvaluatedParameter x
evaluate (Vect xs) = EvaluatedVect children v
  where
    children = map evaluate xs
    v = map value children    
evaluate (x + y) = EvaluatedAdd evaluatedX evaluatedY (add (value evaluatedX) (value evaluatedY))
  where
    evaluatedX = evaluate x 
    evaluatedY = evaluate y
evaluate (x . y) = EvaluatedDot (evaluate x) (evaluate y) $ dotProduct (value (evaluate x)) (value (evaluate y))

run : MonadState Int m => Int -> m ()
run x = do
  modify (+x)
  

main : IO ()
main = do
  putStrLn $ show aGate
  putStrLn "->"
  putStrLn $ show $ evaluate aGate

evaluated : Evaluated Double
evaluated = EvaluatedAdd (EvaluatedParameter 1) (EvaluatedParameter 2) 3 

x : Evaluated (Vect 2 Double)
x = EvaluatedVect [EvaluatedParameter 1, EvaluatedParameter 2] [1,2]

y : Evaluated (Vect 2 Double)
y = EvaluatedVect [EvaluatedAdd (EvaluatedParameter 2) (EvaluatedParameter 0) 2, EvaluatedParameter 2] [2, 2]

anotherEvaluated : Evaluated Double
anotherEvaluated = EvaluatedDot x y 6

input1 : Gate Double
input1 = Parameter 1

input2 : Gate Double
input2 = Parameter 2

input3 : Gate Double 
input3 = Parameter 3

sum : Gate Double
sum = input1 + (input2 + input3)


v : Gate (Vect 2 Double)
v = Vect [Parameter 1, Parameter 2]

dot : Gate Double
dot = Vect [Parameter 1, Parameter 2, Parameter 3] . Vect [Parameter 2, Parameter 3, Parameter 4] 

--aGate : Gate 2 1
--aGate = 1 >:: 2 >:: 3 ::> Nil

--Show (Gate x y)  where
--    show x = let (inputs, outputs) = counts x in  (show inputs) ++ ">::>" ++ (show outputs)

--main : IO ()
--main = putStrLn $ show aGate 
