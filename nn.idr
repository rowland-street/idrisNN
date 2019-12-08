module Main 
import Data.Vect
import Control.Monad.State

interface Add a where
  add : a -> a -> a
interface Mult a where
  mult : a -> a -> a
interface Subtract a where 
  subtract : a -> a -> a
interface Scale a where
  scale : Double -> a -> a

Add Double where
  add = (+)
Mult Double where
  mult = (*)
Scale Double where 
  scale = (*)
Subtract Double where
  subtract = (-)

data Gate : Type -> Type -> Type where
  Fixed : Show a => a -> Gate a s
  Parameter : (Show a, Mult a, Subtract a, Scale a)  => (s -> a) -> (s -> a -> s) -> Gate a s
  Vect : Show a => Vect (S n) (Gate a s) -> Gate (Vect (S n) a) s
  (+) : (Show a, Add a) => Gate a s -> Gate a s -> Gate a s
  (.) : (Add a, Mult a, Show a) => Gate (Vect (S n) a) s -> Gate (Vect (S n) a) s -> Gate a s
  (*) : (Show a, Mult a) => Gate a s -> Gate a s -> Gate a s
  MeanSquaredError : (Show a, Mult a, Subtract a, Scale a) => Gate a s -> Gate a s -> Gate a s  

interface Show a => IEvaluated a where
  val : a -> a

Show (Gate a s) where
  show (Fixed x) = show x
  show (Parameter  _ _) = "p"  
  show (a + b) = show a ++ " + " ++ (show b)
  show (a . b) = show a ++ " . " ++ (show b)
  show (Vect x) = "[ " ++ (show (map show x)) ++ " ]" 
  show (a * b) = show a ++ " x " ++ (show b)
  show (MeanSquaredError a b) = "MSE(" ++ (show a) ++ "," ++ (show b) ++ ")"

-- todo these always have the same interfaces etc also feels constructor maybe able to take a gate
data Evaluated : Type -> Type -> Type where
  EvaluatedFixed : Show a => a -> Evaluated a s
  EvaluatedParameter : (Show a, Mult a, Subtract a, Scale a)  => (s -> a) -> (s -> a -> s) -> Evaluated a s
  EvaluatedVect : Show a => Vect (S n) (Evaluated a s) -> Vect (S n) a -> Evaluated (Vect (S n) a) s
  EvaluatedAdd : (Show a, Add a) => Evaluated a s -> Evaluated a s -> a ->  Evaluated a s
  EvaluatedDot : (Add a, Mult a, Show a) => Evaluated (Vect (S n1) a) s -> Evaluated (Vect (S n1) a) s -> a -> Evaluated a s
  EvaluatedMult : (Show a, Mult a) => Evaluated a s -> Evaluated a s -> a -> Evaluated a s
  EvaluatedMeanSquaredError : (Show a, Mult a, Subtract a, Scale a) => Evaluated a s -> Evaluated a s -> a -> Evaluated a s

--todo write in terms of show Gate
Show (Evaluated a s) where
  show (EvaluatedFixed x) = show x
  show (EvaluatedParameter _ _)  = "p" 
  show (EvaluatedVect x y) = "([ " ++ (show (map show x)) ++ " ] = " ++ (show y) ++ " )"
  show (EvaluatedAdd x y z) = "( " ++  (show x) ++ " + " ++ (show y) ++ " = " ++ (show z) ++ " )"
  show (EvaluatedDot x y z) = "( " ++  (show x) ++ " . " ++ (show y) ++ " = " ++ (show z) ++ " )"
  show (EvaluatedMult x y v) = "( " ++ (show x) ++ " x " ++ (show y) ++ " )"
  show (EvaluatedMeanSquaredError x y v) = "MSE(" ++ (show x) ++ "," ++ (show y) ++ "=" ++ (show v) ++ ")"

value : MonadState b m => Evaluated a b -> m a 
value (EvaluatedFixed x) = pure x
value (EvaluatedParameter get _) = gets get
value (EvaluatedVect _ ys) = pure ys
value (EvaluatedAdd _ _ z) = pure z 
value (EvaluatedDot _ _ w) = pure w
value (EvaluatedMult  _ _ v) = pure v
value (EvaluatedMeanSquaredError _ _ v) = pure v

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

-- todo the mean bit e.g. 1 / 2 or n if its a vec
mse : (Mult a, Subtract a) => a -> a -> a
mse x y = let diff =  subtract x y in 
              mult diff diff

-- todo extract binary function ?
forwardPass : MonadState b m => Gate a b -> m (Evaluated a b)
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
forwardPass (x * y) = do
  evaluatedX <- forwardPass x
  evaluatedY <- forwardPass y
  vx <- value evaluatedX
  vy <- value evaluatedY
  pure $ EvaluatedMult evaluatedX evaluatedY $ mult vx vy
forwardPass (MeanSquaredError x y) = do
  evaluatedX <- forwardPass x
  evaluatedY <- forwardPass y
  vx <- value evaluatedX
  vy <- value evaluatedY
  pure $ EvaluatedMeanSquaredError evaluatedX evaluatedY $ mse vx vy


updateParameter : (MonadState s m, Scale a, Subtract a, Mult a) => (s ->a) -> (s -> a -> s) -> a -> m ()
updateParameter getter setter gradient = do
  existingValue <- gets getter
  let newValue = subtract existingValue $ scale 0.01 $ mult existingValue gradient
  modify $ \s => setter s newValue


backProp : MonadState s m  => a -> Evaluated a s -> m ()
backProp gradient (EvaluatedFixed x) = pure ()
backProp gradient (EvaluatedParameter get set) = updateParameter get set gradient
backProp gradient (EvaluatedAdd x y sum) = do
  backProp gradient x
  backProp gradient y
backProp gs (EvaluatedVect xs vs) = do
  -- todo do I need to scale thes by the forward pass ?
  traverse (uncurry backProp) $ zip gs xs
  pure () 
backProp gradient (EvaluatedMult x y v) = do
  valueX <- value x
  valueY <- value y
  backProp (mult valueX gradient) x
  backProp (mult valueY gradient) y
backProp gradient (EvaluatedMeanSquaredError x y v) = do
  valueX <- value x
  valueY <- value y
  backProp (scale 2 (mult (subtract valueX valueY) gradient)) x
  backProp (scale 2 (mult (subtract valueY valueX) gradient)) y
-- todo .
backProp _ _ = pure ()


run : MonadState Int m => Int -> m ()
run x = modify (+x)
  
increment : MonadState Integer m => Integer -> m ()
increment x = modify $ \i => i + x

traverseTest : MonadState Integer m => Vect n Integer ->  m ()
traverseTest ins = do
  traverse increment ins
  pure ()


learn : MonadState s m => Integer -> Gate Double s ->  m ()
learn 0 _ = pure ()
learn epochs gate = do
  f <- forwardPass gate
  backProp 1.0 f
  learn (epochs - 1) gate
   

learn_ : IO ()
learn_ = do
  let w = Parameter p1 s1
  let bias = Fixed 4.0
  let y = Fixed 7.5
  let x = Fixed 2.0
  let result = w * x + bias
  let loss = MeanSquaredError result y 
  putStrLn $ show $ runState (learn 1000 loss) $ MkParameters 0.1



main : IO ()
main = do
  learn_
  putStrLn $ show $ runState (traverseTest [1,2,3,4,3,2,1]) 0
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
