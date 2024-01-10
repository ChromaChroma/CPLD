{-# LANGUAGE LambdaCase #-}
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
  | Closure VEnv Bind
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
msInFinalState (MS s _ (Ret value)) = null s && isTerminatingValue value
  where
    isTerminatingValue :: Value -> Bool
    isTerminatingValue (I _)         = True
    isTerminatingValue (B _)         = True
    isTerminatingValue Nil           = True
    isTerminatingValue (Cons _ next) = isTerminatingValue next
    isTerminatingValue _             = False

-- returns the final value if machine is in final state. If the machine is not in final state, throw an error
msGetValue :: MachineState -> Value
msGetValue (MS _ _ (Eval _))   = error "AbstractMachineError::Machine State is not in a final state, Machine is in Eval State"
msGetValue ms@(MS _ _ (Ret e)) = if msInFinalState ms then e else error "AbstractMachineError:: Machine State is not in a final state"

msStep :: MachineState -> MachineState
-- ======Ret Mode Patterns===== --
msStep (MS s                                                  env (Ret (Application ex))) = MS s env (Eval ex)
msStep (MS []                                                 _   (Ret _               )) = error "IllegalOperation::Cannot step when final state has been reached"
msStep (MS (EnvValue env'                                : s) _   (Ret val             )) = MS s env' (Ret val) -- Recover previous env
msStep (MS (AddEnv ident : AddEnv identt                 : s) env (Ret val             )) = MS (AddEnv identt : s) (env `E.add` (ident, val)) (Ret val) --Slight hack adding a env double (based on let g = recfunc f, for example)
msStep (MS (AddEnv ident : Application e2                : s) env (Ret val             )) = MS s (env `E.add` (ident, val)) (Eval e2)
msStep (MS (Closure _    (Bind _     _  []           _ ) : _) _   (Ret _               )) = error "IllegalOperation::Cannot apply closure without arguments on a return value"
msStep (MS (Closure env' (Bind _     _t [arg]        ex) : s) env (Ret val             )) = MS (EnvValue env : s) (env' `E.add` (arg, val)) (Eval ex)
msStep (MS (Closure env' (Bind ident _t (arg : args) ex) : s) env (Ret val             )) = let newEnv = env' `E.add` (arg, val)
                                                                                            in MS (EnvValue env : s) newEnv (Ret $ Closure newEnv (Bind ident _t args ex))--TODO: Maybe add illegal character to Ident to not get invalid Recfunc closure in env
msStep (MS (Func f                                       : s) env (Ret val             )) = MS s env (Ret $ f val)
msStep (MS (Application e2                               : s) env (Ret val             )) = case val of
                                                                                              c@Closure {} -> MS (c : s) env (Eval e2)
                                                                                              func -> MS (Func (applyFunc func) : s) env (Eval e2) --Assumed func will be a Func
msStep (MS (sf                                           : _) _   (Ret val             )) = error $ "NotImplemented::Not implemented return state: { stack: " ++ show sf ++ " , return value: " ++ show val ++ " }"

-- ======Eval Mode Patterns===== --
msStep (MS s env (Eval (Var ident                             ))) = MS s env (Ret $ lookupVar env ident)
msStep (MS s env (Eval (Num i                                 ))) = MS s env (Ret $ I i)
msStep (MS s env (Eval (Con "True"                            ))) = MS s env (Ret $ B True)
msStep (MS s env (Eval (Con "False"                           ))) = MS s env (Ret $ B False)
msStep (MS s env (Eval (Con "Nil"                             ))) = MS s env (Ret Nil)
msStep (MS s env (Eval (Con "Cons"                            ))) = MS s env (Ret (Func (Func . runCons)))
msStep (MS s env (Eval (Prim op                               ))) = MS s env (Ret (Func $ if isUnaryOp op then applyUnaryOp op else Func . applyOp op))
msStep (MS s env (Eval (App e1 e2                             ))) = MS (Application e2 : s) env (Eval e1)
msStep (MS s env (Eval (If g e1 e2                            ))) = MS (iteFunc : s) env (Eval g)
                                                                    where iteFunc = Func $ \case
                                                                            B True -> Application e1
                                                                            B False -> Application e2
                                                                            _ -> error "IllegalType::Expected Bool return value (For resolving the guard of IfThenElse)"
msStep (MS s env (Eval (Let [] ex                            ))) = MS s env (Eval ex)
msStep (MS s env (Eval (Let (Bind ident   _  [] ex : bs) body))) = MS (AddEnv ident : Application (Let bs body) : s) env (Eval ex)
msStep (MS s env (Eval (Let (b@(Bind ident _ _ _ ) : bs) body))) = MS (AddEnv ident : Application (Let bs body) : s) env (Ret $ Closure env b)
msStep (MS s env (Eval r@(Recfun (Bind identt _t [] ex)      ))) = MS s (env `E.add` (identt, Application r)) (Eval ex) -- Eval ex, as there are no more input args
msStep (MS s env (Eval r@(Recfun b@(Bind identt _ _ _)  ))) = MS s env (Ret $ Closure (env `E.add` (identt, Application r)) b)
msStep (MS _ _   (Eval other                                  )) = error $ "NotImplemented::Not implemented expression: " ++ show other

lookupVar :: VEnv -> String -> Value
lookupVar env name = case env `E.lookup` name of
  Just val -> val
  Nothing -> error $ "UnknownVariable::Free variable in expression: " ++ show name

runCons :: Value -> Value -> Value
runCons e1 e2 = case (e1, e2) of
  (I i, Nil)          -> Cons i Nil
  (I i, c@(Cons _ _)) -> Cons i c
  (_, _)              -> error "IllegalType::Can only run Cons against Integer values or other list constructors (Cons, Nil)"

applyFunc :: Value -> Value -> Value
applyFunc (Func f) e2 = f e2
applyFunc v        _  = error $ "Error when applying Func " ++ show v

isUnaryOp :: Op -> Bool
isUnaryOp Neg  = True
isUnaryOp Head = True
isUnaryOp Tail = True
isUnaryOp Null = True
isUnaryOp _    = False

applyUnaryOp :: Op -> Value -> Value
applyUnaryOp op v = case op of
  Neg  -> case v of
            I i -> I (-1 * i)
            _ -> error "IllegalType::Cannot invert non-integer values"
  Head -> case v of
            Cons i _  -> I i
            Nil       -> error "IllegalIndex::Cannot run Head on empty list"
            _         -> error "IllegalType::Can only run Head on arrays"
  Tail -> case v of
            Cons _ cs -> cs
            Nil       -> error "IllegalIndex::Cannot run Tail on empty list"
            _         -> error "IllegalType::Can only run Tail on arrays"
  Null -> case v of
            Nil       -> B True
            Cons _ _  -> B False
            _         -> error "IllegalType::Can only run Null on arrays"
  _ -> error "IllegalOperation::Cannot run binary operator as unary operator"

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
  _     -> error "IllegalOperation::Cannot run unary operator as binary operator"
  where
    applyDiv :: Value -> Value -> Value
    applyDiv _      (I 0)  = error "DivideByZero::Cannot divide by zero"
    applyDiv (I i1) (I i2) = I (i1 `div` i2)
    applyDiv (Func f) v2   = Func $ \x -> applyDiv (f x) v2
    applyDiv v1 (Func f2)  = Func $ \x -> applyDiv v1 (f2 x)
    applyDiv _ _           = error $ "IllegalOperation::Cannot apply operator: " ++ show Sub

    applyInt :: (Integer -> Integer -> Integer) -> Value -> Value -> Value
    applyInt op (I i1) (I i2) = I (op  i1 i2)
    applyInt op (Func f) v2   = Func $ \x -> applyInt op (f x) v2
    applyInt op v1 (Func f2)  = Func $ \x -> applyInt op v1 (f2 x)
    applyInt op _ _           = error $ "IllegalOperation::Cannot apply operator: " ++ show op

    applyIntComp :: (Integer -> Integer -> Bool) -> Value -> Value -> Value
    applyIntComp op (I i1) (I i2) = B (op i1 i2)
    applyIntComp op (Func f) v2   = Func $ \x -> applyIntComp op (f x) v2
    applyIntComp op v1 (Func f2)  = Func $ \x -> applyIntComp op v1 (f2 x)
    applyIntComp op _ _           = error $ "IllegalOperation::Cannot apply operator: " ++ show op

    applyEquality :: Value -> Value -> Value
    applyEquality (I i1) (I i2) = B (i1 == i2)
    applyEquality (B b1) (B b2) = B (b1 == b2)
    applyEquality (Func f) v2   = Func $ \x -> applyEquality (f x) v2
    applyEquality v1 (Func f2)  = Func $ \x -> applyEquality v1 (f2 x)
    applyEquality _ _           = error "IllegalOperation::Cannot run equality operator on values of different types (Lists equality not implemented yet)"

    applyInequality :: Value -> Value -> Value
    applyInequality (I i1) (I i2) = B (i1 /= i2)
    applyInequality (B b1) (B b2) = B (b1 /= b2)
    applyInequality (Func f) v2   = Func $ \x -> applyEquality (f x) v2
    applyInequality v1 (Func f2)  = Func $ \x -> applyEquality v1 (f2 x)
    applyInequality _ _           = error "IllegalOperation::Cannot run equality operator on values of different types (Lists equality not implemented yet)"
