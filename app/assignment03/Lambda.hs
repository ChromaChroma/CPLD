{-# OPTIONS -Wall #-}
module Lambda where

import Data.Char
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Text.Show.Functions ()
import Data.Bifunctor (first)

data Token
  = TNum Int
  | TVar String
  | TLambda
  | TApply
  | TAdd
  | TMult
  deriving (Eq, Show)

data Expr
  = Num Int
  | Var String
  | Lambda Expr Expr
  | Apply Expr Expr
  | Mult
  | Add
  deriving (Eq, Show)

data Value = VInt Int | VFun (Value -> Value)
  deriving (Show)

-- | Lexes lambda expression string into tokens
lexer :: String -> [Token]
lexer []                        = []
lexer (' ' : cs)                = lexer cs
lexer ('`' : cs)                = TApply : lexer cs
lexer ('#' : cs)                = TLambda : lexer cs
lexer cs
  | digits /= []          = TNum (read digits :: Int) : lexer digitsRest
  | alphanumeric == "add" = TAdd : lexer alphanumericRest
  | alphanumeric == "mul" = TMult : lexer alphanumericRest
  | alphanumeric /= []    = TVar alphanumeric : lexer alphanumericRest
  | otherwise             = error "LambdaLexer: invalid input"
  where
    (digits, digitsRest) = span isDigit cs
    (alphanumeric, alphanumericRest) = span isLetter cs

-- | Parser expression for list of Labda expression tokens
parser :: [Token] -> Expr
parser tkns = let (e, ts) = parseExpr tkns in if null ts then e
  else error "Parser: Parsing complete, but still tokens left"
  where
    parseExpr :: [Token] -> (Expr, [Token])
    parseExpr tokens = parseLambda tokens

    parseValue :: [Token] -> (Expr, [Token])
    parseValue (TNum n : tokens) = (Num n, tokens) -- Num
    parseValue (TVar v : tokens) = (Var v, tokens) -- Var
    parseValue ts                = error $ "Invalid expression" ++ show ts

    parseOperators :: [Token] -> (Expr, [Token])
    parseOperators (TMult : tokens) = (Mult, tokens) -- Mul
    parseOperators (TAdd : tokens) = (Add, tokens) -- Add
    parseOperators tokens = parseValue tokens

    parseApply :: [Token] -> (Expr, [Token]) -- Apply
    parseApply (TApply : tokens) = (Apply e1 e2, rest') where
      (e1, rest ) = parseExpr tokens
      (e2, rest') = parseExpr rest
    parseApply tokens = parseOperators tokens
    
    parseLambda :: [Token] -> (Expr, [Token])
    parseLambda (TLambda : tokens) = case e1 of  -- Lambda
      (Var v) -> first (Lambda $ Var v) (parseExpr rest)
      _       -> error "LambdaParser: Var expected after lambda notation"
      where (e1, rest) = parseExpr tokens
    parseLambda tokens = parseApply tokens

-- | Evaluates an expression into a Value
-- | Substitute: Base case String is empty (cannot match variables) 
eval :: Expr -> Value
eval = eval' Map.empty .substitute

  where
    eval' :: Map String Value -> Expr -> Value
    eval' _   (Num x)                           = VInt x
    eval' env (Var v)                           = env Map.! v
    eval' _   Add                               = VFun $ VFun . (|+|)
    eval' _   Mult                              = VFun $ VFun . (|*|)
    eval' env (Apply Add e2)                    = VFun (eval' env e2 |+|)
    eval' env (Apply Mult e2)                   = VFun (eval' env e2 |*|)
    eval' env (Apply (Lambda (Var var) body) e2)= eval' (Map.insert var (eval' env e2) env) body
    eval' env (Lambda (Var var) body)           = VFun $ \f -> eval' (Map.insert var f env) body
    eval' env (Apply e1 e2)                     = case eval' env e1 of
      (VFun f) -> f (eval' env e2)
      _ -> error "Cannot apply value like a function to anothe value"
    eval' env e                                   = error $ "Eval: Error during evaluation, not matched pattern :: " ++ show e ++ "::ENV:: " ++ show env

-- | Substitutes expressions applied to expressions by 'inlining' 
-- |  i.e. lambda applied to another expression replaces the lambda variables occurences with the expression
--    Empty string will never match vars, thus placeholder
--    Becaue empty string will never match the given expr will never be bound, also placeholder (-1, could indicate error in output to user)
substitute :: Expr -> Expr
substitute = substitute' "" (Num $ -1)
  where 
    -- | Inner substitution function, replaces variables of given string with expression
    substitute' :: String -> Expr -> Expr -> Expr
    substitute' _ _ (Num x)                           = Num x
    substitute' s e (Var var)                         = if var == s then e else Var var
    substitute' _ _ Add                               = Add
    substitute' _ _ Mult                              = Mult
    substitute' s e (Apply (Lambda (Var v) body) e2)  = substitute' v (substitute' s e e2) (substitute' s e body) -- substitute' the lambda body before total substitution to work away duplicate variables
    substitute' s e (Apply e1 e2)                     = Apply (substitute' s e e1) (substitute' s e e2)
    substitute' s e (Lambda (Var v) body)             = Lambda (Var v) (substitute' s e body)
    substitute' _ _ _                                 = error "Substitution: Error occured during substitution of lambda abstractions"


-- | Operators for runOp of addition and multiplication
(|+|), (|*|) :: Value -> Value -> Value
(|+|) = runOp (+)
(|*|) = runOp (*)

infixl 9 |+|

infixl 9 |*|

-- | Runs an binary integer operator on the Value wrapper
runOp:: (Int -> Int -> Int) -> Value -> Value -> Value
runOp op e1 e2 = case (e1, e2) of
  (VInt i, VInt j) -> VInt $ op i j
  (VFun f, VInt j) -> VFun $ \val -> runOp op (f val)  (VInt j)
  (VInt i, VFun g) -> VFun $ \val -> runOp op (VInt i) (g val)
  (VFun f, VFun g) -> VFun $ \val -> VFun (runOp op (f val) . g)
  -- (VFun f, VFun g) -> VFun $ VFun . (runOp op) . g . f

-- | Parser function used for debugging purposes
pp :: Expr -> String
pp (Apply e1 e2)        = '(' : pp e1 ++ ") (" ++ pp e2 ++ ")"
pp (Lambda (Var v) e2)  = "_" ++ v ++ " -> {" ++ pp e2 ++ "}"
pp (Num i)              = show i
pp (Var v)              = v
pp Add                  = "add"
pp Mult                 = "mul"
pp _                    = "<Some invalid>"

-- | Combines evaluation, parsing and lexing
interpret :: String -> Value
interpret  = eval . parser . lexer
