module MinHS.Evaluator where

import Data.Bool (Bool (False, True))
import Debug.Trace
import qualified MinHS.Env as E
import MinHS.Pretty
import MinHS.Syntax
import qualified Prettyprinter as PP
import Prettyprinter.Render.Terminal (AnsiStyle)
import Text.Show.Functions ()

-- do not change this definition
evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE e
evaluate _ = error "Input program did not have exactly one binding"

-- do not change this definition
evalE :: Exp -> Value
evalE expr = loop (msInitialState expr)
  where
    loop ms =
      (trace $ "debug message:" ++ show ms) $  -- uncomment this line and pretty print the machine state/parts of it to
      -- observe the machine states
      if (msInFinalState newMsState)
        then msGetValue newMsState
        else loop newMsState
      where
        newMsState = msStep ms

type VEnv = E.Env Value

data Value
  = I Integer
  | B Bool
  | Nil
  | Cons Integer Value
  | Func (Value -> Value)
  | PartialFunc Value Exp -- Expected Value to be Func with a Func inside (multiple arguments expected)
  -- Add other variants as needed
  -- deriving (Show, Read)
  deriving (Show)

-- instance Read Value where 
--   read v = 
--   readsPrec _ input =
--     let (_, r) = span (/= ' ') input
--     in if not $ null r case r of
--       "True" -> B True
--       "False" -> B False
--       "[" -> let (_, r') = span (/= ' ') (tail r)
--                   f  rr = case rr of 
--                 "]" -> Nil 
--                 x   -> let (dig, r'') = span (isDigit) c
--                         in Cons dig (f r'') 
--       other -> if isDigit other 
--         then I (read other :: Int )
--         else 


prettyValue :: Value -> PP.Doc AnsiStyle
prettyValue (I i) = numeric i
prettyValue (B b) = datacon (show b)
prettyValue (Nil) = datacon "Nil"
prettyValue (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> prettyValue v)

data MachineState = MS -- add the definition
  [Value] -- Control stack
  VEnv    -- Environment
  -- Maybe Exp     -- Current expression
  Mode    -- Mode the machine is in
  deriving (Show)
  
data Mode = Eval Exp | Ret Value deriving (Show)

msInitialState :: Exp -> MachineState
msInitialState e = MS [] E.empty (Eval e) 


-- checks whether machine is in final state
msInFinalState :: MachineState -> Bool
msInFinalState (MS _ _   (Eval _))    = False
msInFinalState (MS s env (Ret value)) = null s && null env &&  isTerminatingValue value
  where
    isTerminatingValue :: Value -> Bool
    isTerminatingValue (I _)         = True
    isTerminatingValue (B _)         = True
    isTerminatingValue (Nil)         = True
    isTerminatingValue (Cons _ next) = isTerminatingValue next
    isTerminatingValue _             = False

-- returns the final value if machine is in final state. If the machine is not in final state, throw an error
msGetValue :: MachineState -> Value
msGetValue (MS _ _ (Eval _))   = error "Machine State is not in a final state: Machine is in Eval State"
msGetValue ms@(MS _ _ (Ret e)) =
  if msInFinalState ms
    then e
    else error "Machine State is not in a final state."

msStep :: MachineState -> MachineState
msStep (MS []                     _   (Ret _ ) ) = error "Cannot step when final value has been reached"
msStep (MS (Func f           : s) env (Ret val)) = MS s env (Ret $ f val)
msStep (MS (PartialFunc f e2 : s) env (Ret val)) = MS ( Func (\v -> applyFunc (applyFunc f val) v) : s) env (Eval e2)
msStep (MS s                      _   (Ret val)) = error $ "Some other state when ret: " ++ show s ++ " :: " ++ show val
msStep (MS s                      env (Eval e) ) = case e of
  Var ident -> case E.lookup env ident of 
    Just val -> MS s env (Ret val)
    Nothing  -> error "Invalid expression: free variable in expression"
  Num i       -> MS s env (Ret $ I i) 
  Con "True"  -> MS s env (Ret $ B True)
  Con "False" -> MS s env (Ret $ B False)
  Con "Nil"   -> MS s env (Ret Nil)         -- TODO: add Cons
  Con "Cons"  -> MS s env (Ret (Func (\val -> Func (\next -> runCons val next))))
  App e1 e2   -> MS (PartialFunc (Func id) e2:s) env (Eval e1)
  Prim op -> MS s env . Ret . Func $ if isUnaryOp op 
    then applyUnaryOp op
    else \x ->  Func (applyOp op x)
    -- if isUnaryOp op 
    -- then MS s env (Ret $ Func (applyUnaryOp op))
    -- else MS s env (Ret $ Func (\x ->  Func (applyOp binOp x)))

  other -> error $ "Not Implemented: " ++ show other

isUnaryOp :: Op -> Bool 
isUnaryOp Neg  = True
isUnaryOp Head = True
isUnaryOp Tail = True
isUnaryOp Null = True
isUnaryOp _    = False

applyFunc :: Value -> Value -> Value 
applyFunc (Func f) e2 = f e2
applyFunc _ _         = error "Error when applying Func"

runCons :: Value -> Value -> Value 
runCons e1 e2 = case (e1, e2) of
  (I i, Nil         ) -> Cons i Nil
  (I i, c@(Cons _ _)) -> Cons i c
  (_,   _           ) -> error "Can only run Cons against Integer values and more Cons"

applyUnaryOp :: Op -> Value -> Value
applyUnaryOp op v = case op of 
  Neg  -> case v of 
    I i -> I (-1 * i)
    _ -> error "Cannot invert non integer values" -- Maybe later this also for bools?
  Head -> case v of
    Cons i _  -> I i
    Nil       -> error "Cannot run Head on empty list"
    _         -> error "Can only run Head on array values"
  Tail -> case v of
    Cons _ cs -> cs
    Nil       -> error "Cannot run Tail on empty list"
    _         -> error "Can only run Tail on array values"
  Null -> case v of 
    Nil       -> B True
    Cons _ _  -> B False
    _         -> error "Can only run Null on array values"
  _ -> error "Cannot run binary operator as unary operator"

applyOp :: Op -> Value -> Value -> Value
applyOp operator v v' = case operator of 
  Add   -> applyInt      (+)  v v'
  Sub   -> applyInt      (-)  v v'
  Mul   -> applyInt      (*)  v v'
  Quot  -> applyDiv           v v'
  Rem   -> applyInt      mod  v v'
  Gt    -> applyIntComp  (>)  v v'
  Ge    -> applyIntComp  (>=) v v'
  Lt    -> applyIntComp  (<)  v v'
  Le    -> applyIntComp  (<=) v v'
  Eq    -> applyEquality      v v'
  Ne    -> applyInequality      v v'
  _     -> error "Cannot run unary operator as binary operator"
  where 
    applyDiv ::  Value -> Value -> Value
    applyDiv _      (I 0)  = error "Cannot divide by zero"
    applyDiv (I i1) (I i2) = I (i1 `div` i2)
    applyDiv (Func f) v2   = Func $ \x -> applyDiv (f x) v2
    applyDiv v1 (Func f2)  = Func $ \x -> applyDiv v1 (f2 x)
    applyDiv _ _           = error $ "Cannot apply operator: " ++ show Sub

    applyInt :: (Integer -> Integer -> Integer) -> Value -> Value -> Value
    applyInt op (I i1) (I i2) = I (op  i1 i2)
    applyInt op (Func f) v2   = Func $ \x -> applyInt op (f x) v2
    applyInt op v1 (Func f2)  = Func $ \x -> applyInt op v1 (f2 x)
    applyInt op _ _           = error $ "Cannot apply operator: " ++ show op

    applyIntComp :: (Integer -> Integer -> Bool) -> Value -> Value -> Value
    applyIntComp op (I i1) (I i2) = B (op i1 i2)
    applyIntComp op (Func f) v2   = Func $ \x -> applyIntComp op (f x) v2
    applyIntComp op v1 (Func f2)  = Func $ \x -> applyIntComp op v1 (f2 x)
    applyIntComp op _ _            = error $ "Cannot apply operator: " ++ show op

    applyEquality :: Value -> Value -> Value
    applyEquality (I i1) (I i2) = B (i1 == i2)
    applyEquality (B b1) (B b2) = B (b1 == b2)
    applyEquality (Func f) v2   = Func $ \x -> applyEquality (f x) v2
    applyEquality v1 (Func f2)  = Func $ \x -> applyEquality v1 (f2 x)
    applyEquality _ _            = error "Cannot run equality operator on values because they are different types or: (Lists equality not implemented yet)"
    
    applyInequality :: Value -> Value -> Value
    applyInequality (I i1) (I i2) = B (i1 /= i2)
    applyInequality (B b1) (B b2) = B (b1 /= b2)
    applyInequality (Func f) v2   = Func $ \x -> applyEquality (f x) v2
    applyInequality v1 (Func f2)  = Func $ \x -> applyEquality v1 (f2 x)
    applyInequality _ _            = error "Cannot run equality operator on values because they are different types or: (Lists equality not implemented yet)"



{- 
  Small Step Semantics, Manual steps
-}

{- Small Step Semantics: Sub -}
-- .                                                                        => (App (App (Prim Sub) (Num 3)) (Num 2))
-- (App <> (Num 2)) | .                                                     => (App (Prim Sub) (Num 3))
-- (App <> (Num 3)) | (App <> (Num 2)) | .                                  => (Prim Sub)
-- (App <> (Num 3)) | (App <> (Num 2)) | .                                  <= Ret (Func(\x -> Func \y -> x - y))
-- (App Ret (Func(\x -> Func \y -> x - y)) <>) | (App <> (Num 2)) | .       => (Num 3)
-- (App Ret (Func(\x -> Func \y -> x - y)) <>) | (App <> (Num 2)) | .       <= Ret 3
-- (App <> (Num 2)) | .                                                     <= Ret (Func \y -> 3 - y)
-- (App Ret (Func \y -> 3 - y) <>) | .                                      => (Num 2)
-- (App Ret (Func \y -> 3 - y) <>) | .                                      <= Ret 2
-- .                                                                        <= Ret 1        

{- Small Step Semantics: Cons and Nil -}
-- .                                                                        => (App (App (Con "Cons") (Num 1)) (Con "Nil"))
-- (App <> (Con "Nil")) | .                                                 => (App (Con "Cons") (Num 1))
--
-- (App <> (Num 1)) | (App <> (Con "Nil")) | .                              => (Con "Cons")
--
-- (App <> (Num 1)) | (App <> (Con "Nil")) | .                              <= Ret Func(\x -> Func \y -> Cons x y)
-- (App Ret Func(\x -> Func \y -> Cons x y) <>) | (App <> (Con "Nil")) | .  => (Num 1)
-- (App Ret Func(\x -> Func \y -> Cons x y) <>) | (App <> (Con "Nil")) | .  <= Ret 1
-- (App <> (Con "Nil")) | .                                                 <= Ret (Func \y -> Cons 1 y)
-- (App Ret (Func \y -> Cons 1 y) <>) | .                                   => (Con "Nil")
-- (App Ret (Func \y -> Cons 1 y) <>) | .                                   <= Ret Nil
-- .                                                                        <= Cons 1 Nil

{- Small Step Semantics: Apply Binary Operator -}
-- .                                      => (App (App (Prim op) e1) e2)
-- App <> e2 | .                          => (App (Prim op) e1)
-- (App <> e1) | (App <> e2) | .          => (Prim op)
-- (App <> e1) | (App <> e2) | .          <= Ret (\x -> \x' -> op x x')     --Ret Func for short
-- (App (Ret Func) <>) | (App <> e2) | .  => e1
-- (App (Ret Func) <>) | (App <> e2) | .  <= e1
-- (App <> e2) | .                        => (\x' -> op e1 x')
-- (App <> e2) | .                        <= Ret (\x' -> op e1 x')
-- .                                      <= Ret (op e1 e2)
