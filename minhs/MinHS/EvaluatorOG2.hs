{-# LANGUAGE LambdaCase #-}
module MinHS.EvaluatorOG2 where

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
      --  (trace $ "debug message:" ++ show ms) $  -- uncomment this line and pretty print the machine state/parts of it to
      -- observe the machine states
      if msInFinalState newMsState
        then msGetValue newMsState
        else loop newMsState
      where
        newMsState = msStep ms

type VEnv = E.Env Value

prettyValue :: Value -> PP.Doc AnsiStyle
prettyValue (I i) = numeric i
prettyValue (B b) = datacon (show b)
prettyValue Nil = datacon "Nil"
prettyValue (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> prettyValue v)

data Value
  = I Integer
  | B Bool
  | Nil
  | Cons Integer Value
  | EnvValue VEnv
  | Closure VEnv String String Exp
  | Func (Value -> Value)
  | Application Exp
  | AddEnv Id
  deriving (Show) -- deriving (Show, Read)

data MachineState = MS
  [Value] -- Control stack
  VEnv    -- Environment
  Mode    -- Mode the machine is in (Exp or Value)
  deriving (Show)

data Mode
  = Eval Exp  -- Mode to evaluate an expression
  | Ret Value -- Mode to return a value
  deriving (Show)

msInitialState :: Exp -> MachineState
msInitialState e = MS [] E.empty (Eval e)


-- checks whether machine is in final state
msInFinalState :: MachineState -> Bool
msInFinalState (MS _ _   (Eval _))    = False
msInFinalState (MS s _ (Ret value)) = null s &&  isTerminatingValue value
  where
    isTerminatingValue :: Value -> Bool
    isTerminatingValue (I _)         = True
    isTerminatingValue (B _)         = True
    isTerminatingValue Nil         = True
    isTerminatingValue (Cons _ next) = isTerminatingValue next
    isTerminatingValue _             = False

-- returns the final value if machine is in final state. If the machine is not in final state, throw an error
msGetValue :: MachineState -> Value
msGetValue (MS _ _ (Eval _))   = error "Machine State is not in a final state: Machine is in Eval State"
msGetValue ms@(MS _ _ (Ret e)) = if msInFinalState ms
  then e
  else error "Machine State is not in a final state."

msStep :: MachineState -> MachineState
msStep (MS stack env (Ret (Application ex))) = MS stack env (Eval ex) -- Used for ITE logic, 
msStep (MS stack env (Ret val)) = case stack of
  []                                -> error "Cannot step when final value has been reached"
  EnvValue env' : s                 -> MS s env' (Ret val) -- Recover previous env
  AddEnv ident : AddEnv identt : s  -> MS (AddEnv identt : s) (env `E.add` (ident, val) ) (Ret val) --Slight hack adding a env double (based on let g = recfunc f, for example)
  AddEnv ident : Application e2 : s -> MS s (env `E.add` (ident, val) ) (Eval e2)
  c@(Closure env' ident arg ex) : s -> let  newEnv = env' `E.add` (ident, c) `E.add` (arg, val)
                                        in  MS (EnvValue env : s) newEnv (Eval ex)
  Func f : s                        -> MS s env (Ret $ f val)
  Application e2 : s                -> case val of
                                        c@Closure {} -> MS (c : s) env (Eval e2)
                                        func         -> MS (Func (applyFunc func) : s) env (Eval e2) --Assumed func will be a Func
  s                                 -> error $ "Some other state when returning: " ++ show s ++ " :: " ++ show val
msStep (MS s env (Eval e)) = case e of
  Var ident                         -> case E.lookup env ident of
                                         Just val -> MS s env (Ret val)
                                         Nothing  -> error $ "Invalid expression: free variable in expression: " ++ show ident
  Num i                             -> MS s env (Ret $ I i)
  Con "True"                        -> MS s env (Ret $ B True)
  Con "False"                       -> MS s env (Ret $ B False)
  Con "Nil"                         -> MS s env (Ret Nil)
  Con "Cons"                        -> MS s env (Ret (Func (Func . runCons)))
  Prim op                           -> MS s env (Ret $ primOpFunc op)
  App e1 e2                         -> MS (Application e2 : s) env (Eval e1)
  If g e1 e2                        -> MS (iteFunc e1 e2 : s) env (Eval g)
  Let [] ex                         -> MS s env (Eval ex)
  Let (Bind ident _ [] ex : bs) body-> case ex of
                                        r@(Recfun (Bind identt _ _ _) ) -> MS (AddEnv identt : AddEnv ident : Application (Let bs body) : s) env (Eval r)
                                        _                               -> MS (AddEnv ident : Application (Let bs body) : s) env (Eval ex) 
  -- TODO: Only implemented for single argument (just like Recfun)
  Let (Bind ident _ [arg] ex: bs) body-> MS (AddEnv ident : Application (Let bs body) : s) env (Ret $ Closure env ident arg ex)

  Recfun (Bind _     _ [] ex)       -> MS s env (Eval ex) -- Eval ex, as there are no more input args
  Recfun (Bind ident _ [arg] ex)    -> MS s env (Ret $ Closure env ident arg ex)
  -- TODO: Recfun (Bind ident t (arg : args) ex) ->               --Multiple Arguments not implemented yet
  other                      -> error $ "Not Implemented: " ++ show other
  where
    primOpFunc op = Func $ if isUnaryOp op
      then applyUnaryOp op
      else Func . applyOp op

    iteFunc e1 e2 = Func $ \case
      B True -> Application e1
      B False -> Application e2
      _ -> error "No Boolean return value for the guard if the IF THEN ELSE expression"


isUnaryOp :: Op -> Bool
isUnaryOp Neg  = True
isUnaryOp Head = True
isUnaryOp Tail = True
isUnaryOp Null = True
isUnaryOp _    = False

applyFunc :: Value -> Value -> Value
applyFunc (Func f) e2 = f e2
applyFunc v _         = error $ "Error when applying Func " ++ show v

runCons :: Value -> Value -> Value
runCons e1 e2 = case (e1, e2) of
  (I i, Nil         ) -> Cons i Nil
  (I i, c@(Cons _ _)) -> Cons i c
  (_,   _           ) -> error "Can only run Cons against Integer values and more Cons"

applyUnaryOp :: Op -> Value -> Value
applyUnaryOp op v = case op of
  Neg  -> case v of
            I i -> I (-1 * i)
            _ -> error "Cannot invert non integer values"
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
  Ne    -> applyInequality    v v'
  _     -> error "Cannot run unary operator as binary operator"
  where
    applyDiv :: Value -> Value -> Value
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

{- Small Step Semantics: Let in Multiple -}
-- . / o                                                                      => (Let [ Bind "x" (Type Int) (Num 1) : b : bs] (Var x))
-- (Let [b : bs] (Var x)) | . / o                                             => Bind "x" (Type Int) (Num 1)
-- (Let [b : bs] (Var x)) | . / o                                             => Bind "x" (Type Int) (Num 1)
-- SetEnv "x" <> | (Let [b : bs] (Var x)) | . / o                             => (Num 1)
-- SetEnv "x" <> | (Let [b : bs] (Var x)) | . / o                             <= Ret 1
-- (Let [bs] (Var x)) | . / o                                                 => b
-- . / x<-1;o                                                                 => (Let [bs] x) 
-- ...
-- SetEnv "ident" <> | (Let [] x) | . / x<-1;...;o                            <= Ret (Num 123)
-- . / x<-1;...;o                                                             => Var x
-- . / x<-1;...;o                                                             <= Ret 1
-- Done

-- (Let <> (Num 1) ] x) | . / o                                               => [ Bind "x" (Type Int) (Num 1)]]
-- (Let <> (Num 1) ] x) | . / o                                               => Bind "x" (Type Int) (Num 1) 
-- SetEnv "x" <> | (Let <> (Num 1) ] x) | . / o                               => (Num 1)
-- SetEnv "x" <> | (Let <> (Num 1) ] x) | . / o                               <= Ret 1
--  . / x<-1;o                                                                <= Var x 
--  . / x<-1;o                                                                <= 1
--  . / o                                                                     <= 1


{- Small Step Semantics: Let in -}
-- . / o                                                                      => (Let [ Bind "x" (Type Int) (Num 1)]] x)
-- (Let <> (Num 1) ] x) | . / o                                               => [ Bind "x" (Type Int) (Num 1)]]
-- (Let <> (Num 1) ] x) | . / o                                               => Bind "x" (Type Int) (Num 1) 
-- SetEnv "x" <> | (Let <> (Num 1) ] x) | . / o                               => (Num 1)
-- SetEnv "x" <> | (Let <> (Num 1) ] x) | . / o                               <= Ret 1
--  . / x<-1;o                                                                <= Var x 
--  . / x<-1;o                                                                <= 1
--  . / o                                                                     <= 1


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

-- debug message:MS 
--   [   Application (App (Prim Head) (Var "xs"))
--     , Func <function>
--     , Application (App (Var "map2") (App (Prim Tail) (Var "xs")))
--     , EnvValue (Env (fromList [  ("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1)))
--                                 ,("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))))
--                                 ,("map2",Closure (Env (fromList [
--                                                                   ("mapInc",Closure (Env (fromList [("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1))),("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))))),("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))
--                                                                   ,("xs",Cons 0 (Cons 1 (Cons 2 Nil)))
--                                                                 ])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))
--                                                               )
--                                 ,("xs",Cons 0 (Cons 1 (Cons 2 Nil)))
--                               ]))
--     ,Func <function>
--     ,EnvValue (Env (fromList [ ("mapInc",Closure (Env (fromList [  ("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1)))
--                                                                   ,("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))))
--                                                                   ,("xs",Cons 0 (Cons 1 (Cons 2 Nil)))
--                                                                 ]))   "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))
--                                                               )
--                               ,("xs",Cons 0 (Cons 1 (Cons 2 Nil)))
--                             ]))]
--   (Env (fromList [
--     ("map2",Closure (Env (fromList [   ("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1)))
--                                       ,("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))))
--                                       ,("map2",Closure (Env (fromList [("mapInc",Closure (Env (fromList [("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1))),("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))))),("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))),("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))
--                                       ,("xs",Cons 0 (Cons 1 (Cons 2 Nil)))
--                                     ])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))
--   ,("mapInc",Closure (Env (fromList [  ("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1)))
--                                       ,("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))))
--                                       ,("xs",Cons 0 (Cons 1 (Cons 2 Nil)))
--                                     ])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))
--   ,("xs",Cons 1 (Cons 2 Nil))

--   ])) 
--   (Eval (Var "f"))


-- debug message:MS 
--   [Func <function>
--   ,EnvValue (Env (fromList [("mapInc",Closure (Env (fromList [("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1))),("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))))),("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))),("xs",Cons 0 (Cons 1 (Cons 2 Nil)))]))
--   ] 
--   (Env (fromList [
--     ("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1)))
--     ,("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))))
--     ,("map2",Closure (Env (fromList [("mapInc",Closure (Env (fromList [("f",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "inc" "x" (App (App (Prim Add) (Var "x")) (Num 1))),("map",Closure (Env (fromList [("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map" "f" (Recfun (Bind "map2" (Arrow (TypeApp (TypeCon List) (TypeCon Int)) (TypeApp (TypeCon List) (TypeCon Int))) ["xs"] (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))))),("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs")))))),("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) "map2" "xs" (If (App (Prim Null) (Var "xs")) (Con "Nil") (App (App (Con "Cons") (App (Var "f") (App (Prim Head) (Var "xs")))) (App (Var "map2") (App (Prim Tail) (Var "xs"))))))
--     ,("xs",Cons 0 (Cons 1 (Cons 2 Nil)))])) 
--   (Eval (App (Prim Null) (Var "xs")))
