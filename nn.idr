module Main 

import Data.Vect

--vadd : Num a => Vect n a -> Vect n a -> Vect n a
--vadd [] [] = ?vadd_rhs_3
--vadd (x :: xs) ys = ?vadd_rhs_2

-- data Vect : Nat -> Type -> Type where
--   Nil  : Vect Z a
--   (::) : a -> Vect k a -> Vect (S k) a

--infixr 7 >::
--infixr 7 ::>

--data Gate : Nat -> Nat -> Type where
--  Nil : Gate Z Z
--  (>::) : Int -> Gate x y -> Gate (S x) y
--  (::>) : Int -> Gate x y -> Gate x (S y)

--countInputs : Gate x y -> Int
--countInputs (x >:: xs) = 1 + countInputs xs
--countInputs _ = 0

--counts : Gate x y -> (Int, Int)
--counts Nil = (0, 0)
--counts (x >:: xs) = let (inputs, outputs) = counts xs in (1 + inputs, outputs)
--counts (x ::> xs) = let (inputs, outputs) = counts xs in  (inputs, 1 + outputs)

interface Add a where
  add : a -> a -> a
interface Mult a where
  mult : a -> a -> a

Add Double where
  add = (+)
Mult Double where
  mult = (*)

data Gate : Type -> Type where
  Parameter : a -> Gate a
  Vect : Vect n (Gate a) -> Gate (Vect n (Gate a))
  (+) : Add a => Gate a  -> Gate a -> Gate a
  (.) : (Add a, Mult a) => Gate (Vect n (Gate a)) -> Gate (Vect n (Gate a)) -> Gate a

data Evaluated : Type -> Type where
  EvaluatedParameter : a -> Evaluated a
  EvaluatedVect : Vect n (Evaluated a) -> Vect n a -> Evaluated (Vect n (Evaluated a))
  EvaluatedAdd : Add a => Evaluated a -> Evaluated a -> a ->  Evaluated a
  EvaluatedDot : (Add a, Mult a) => Evaluated (Vect n (Evaluated a)) -> Evaluated (Vect n (Evaluated a)) -> a -> Evaluated a 

evaluated : Evaluated Double
evaluated = EvaluatedAdd (EvaluatedParameter 1) (EvaluatedParameter 2) 3 

x : Evaluated (Vect 2 (Evaluated Double))
x = EvaluatedVect [EvaluatedParameter 1, EvaluatedParameter 2] [1,2]

anotherEvaluated : Evaluated Double
anotherEvaluated = EvaluatedDot x (EvaluatedVect [EvaluatedAdd (EvaluatedParameter 2) (EvaluatedParameter 0) 2, EvaluatedParameter 2] [2, 2]) 6

input1 : Gate Double
input1 = Parameter 1

input2 : Gate Double
input2 = Parameter 2

input3 : Gate Double 
input3 = Parameter 3

sum : Gate Double
sum = input1 + (input2 + input3)

dot : Gate Double
dot = Vect [Parameter 1, Parameter 2, Parameter 3] . Vect [Parameter 2, Parameter 3, Parameter 4] 

--aGate : Gate 2 1
--aGate = 1 >:: 2 >:: 3 ::> Nil

--Show (Gate x y)  where
--    show x = let (inputs, outputs) = counts x in  (show inputs) ++ ">::>" ++ (show outputs)

--main : IO ()
--main = putStrLn $ show aGate 
