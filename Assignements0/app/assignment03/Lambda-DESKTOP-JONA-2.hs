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
  | Lambda String Expr
  | Apply Expr Expr
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
  | digits /= []                = TNum (read digits :: Int) : lexer digitsRest
  | alphanumeric /= []          = TVar alphanumeric : lexer alphanumericRest -- add and mul are parsed as variables referencing later defined functions
  | otherwise                   = error "LambdaLexer: invalid input"
  where
    (digits, digitsRest)              = span isDigit cs
    (alphanumeric, alphanumericRest)  = span isLetter cs

-- | Parser expression for list of Labda expression tokens
parser :: [Token] -> Expr
parser tkns = if null remaining 
  then e
  else error "Parser: Parsing complete, but still tokens left"
  where
    (e, remaining) = parseExpr tkns 
    parseExpr :: [Token] -> (Expr, [Token])
    parseExpr tokens = parseLambda tokens

    parseValue :: [Token] -> (Expr, [Token])
    parseValue (TNum n : tokens) = (Num n, tokens) -- Num
    parseValue (TVar v : tokens) = (Var v, tokens) -- Var
    parseValue ts                = error $ "Invalid expression" ++ show ts

    parseApply :: [Token] -> (Expr, [Token]) -- Apply
    parseApply (TApply : tokens) = (Apply e1 e2, rest') where
      (e1, rest ) = parseExpr tokens
      (e2, rest') = parseExpr rest
    parseApply tokens = parseValue tokens

    parseLambda :: [Token] -> (Expr, [Token])
    parseLambda (TLambda : tokens) = case e1 of  -- Lambda
      (Var v) -> first (Lambda v) (parseExpr rest)
      _       -> error "LambdaParser: Var expected after lambda notation"
      where (e1, rest) = parseExpr tokens
    parseLambda tokens = parseApply tokens

initialEnv :: Map String Value
initialEnv = Map.fromList [addDef, mulDef]
  where 
    addDef = ("add", VFun $ VFun . runOp (+))
    mulDef = ("mul", VFun $ VFun . runOp (*))

-- | Evaluates an expression into a Value
-- | Substitute: Base case String is empty (cannot match variables) 
eval :: Expr -> Value
eval = eval' initialEnv . substitute
  where
    eval' :: Map String Value -> Expr -> Value
    eval' _   (Num x)           = VInt x
    eval' env (Var v)           = case Map.lookup v env of
      Just (val)  -> val
      Nothing     -> VFun id
    eval' env (Apply e1 e2)     = case eval' env e1 of
      (VFun f) -> f (eval' env e2)
      _ -> error "Cannot apply value like a function to anothe value"
    eval' env (Lambda var body) = VFun (\x -> eval' (Map.insert var x env) body)

-- | Substitutes expressions applied to expressions by 'inlining' 
-- |  i.e. lambda applied to another expression replaces the lambda variables occurences with the expression
--    Empty string will never match vars, thus placeholder
--    Becaue empty string will never match the given expr will never be bound, also placeholder (-1, could indicate error in output to user)
substitute :: Expr -> Expr
substitute = substitute' "" (Num $ -1)
  where
    -- | Inner substitution function, replaces variables of given string with expression
    substitute' :: String -> Expr -> Expr -> Expr
    substitute' _ _ (Num x)                     = Num x
    substitute' s e (Var var)                   = if var == s then e else Var var
    substitute' s e (Apply (Lambda v body) e2)  = substitute' v (substitute' s e e2) (substitute' s e body)
    substitute' s e (Apply e1 e2)               = Apply (substitute' s e e1) (substitute' s e e2)
    substitute' s e (Lambda v body)             = Lambda v (substitute' s e body)

-- | Runs an binary integer operator on the Value wrapper
runOp:: (Int -> Int -> Int) -> Value -> Value -> Value
runOp op e1 e2 = case (e1, e2) of
  (VInt i, VInt j) -> VInt $ op i j
  (VFun f, VInt j) -> VFun $ \val -> runOp op (f val)  (VInt j)
  (VInt i, VFun g) -> VFun $ \val -> runOp op (VInt i) (g val)
  (VFun f, VFun g) -> VFun $ \val -> VFun (runOp op (f val) . g)

-- | Combines evaluation, parsing and lexing
interpret :: String -> Value
interpret  = eval . parser . lexer
