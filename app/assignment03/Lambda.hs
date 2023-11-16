{-# OPTIONS -Wall #-}
module Lambda where

import Data.Char
import Data.Map.Strict (Map, (!))
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
  -- | Apply Expr Expr
  | Lambda Expr Expr
  | Apply Expr Expr
  | Mult 
  | Add 
  deriving (Eq, Show)
  
data Value = VInt Int | VFun (Value -> Value)
  deriving (Show)

-- | Lexes Infix string into tokens
lexer :: String -> [Token]
lexer []                        = []
lexer (' ' : cs)                = lexer cs
lexer ('`' : cs)                = TApply : lexer cs
lexer ('#' : cs)                = TLambda : lexer cs
lexer ('a' :'d' : 'd' : cs)     = TAdd : lexer cs
lexer ('m' :'u' :'l' : cs) = TMult : lexer cs
lexer cs
  | digits /= []        = TNum (read digits :: Int) : lexer digitsRest
  | alphanumeric /= []  = TVar alphanumeric : lexer alphanumericRest
  | otherwise           = error "LambdaLexer: invalid input"
  where 
    (digits, digitsRest) = span isDigit cs
    (alphanumeric, alphanumericRest) = span isLetter cs

-- Parser expression for list of Labda expression tokens
parser :: [Token] -> Expr
parser tokens = let (e, ts) = parseExpr tokens in if null ts 
  then e
  else error $ show e ++"  "++show ts-- "More tokens than able to be parsed, check if there are too many arguments at the end of the string"

parseExpr :: [Token] -> (Expr, [Token])
parseExpr tokens = parseOperators tokens 

parseValue :: [Token] -> (Expr, [Token])
parseValue (TNum n : tokens) = (Num n, tokens) -- Num
parseValue (TVar v : tokens) = (Var v, tokens) -- Var
parseValue ts                = error $"Invalid expression" ++ show ts

parseLambda :: [Token] -> (Expr, [Token])
parseLambda (TLambda : tokens) = case e1 of  -- Lambda
  (Var v) -> first (Lambda $ Var v) (parseExpr rest)
  _       -> error "LambdaParser: Var expected after lambda notion"
  where (e1, rest) = parseExpr tokens
parseLambda tokens = parseValue tokens

parseApply :: [Token] -> (Expr, [Token]) -- Apply
parseApply (TApply : tokens) = (Apply e1 e2, rest') where 
  (e1, rest ) = parseExpr tokens
  (e2, rest') = parseExpr rest
parseApply tokens = parseLambda tokens

parseOperators :: [Token] -> (Expr, [Token])
parseOperators (TMult : tokens) = (Mult, tokens) -- Mul
parseOperators (TAdd : tokens)  = (Add, tokens)  -- Add
parseOperators tokens           = parseApply tokens

-- TODO: Input "``#r#t```r t`add 1 0#f```f f f f#f#x`f`f x " werkt niet, iets wss met recursive apply

-- parseApply :: [Token] -> (Expr, [Token])
-- parseApply (TApply : TApply : tokens) = parseExpr tokens
-- parseApply (TApply : TLambda : tokens) = (Apply left left', rest')
--   where 
--     (left, rest) = parseLambda (TLambda : tokens)
--     (left', rest') = (parseApply rest)
-- parseApply (TApply  : tokens) = (Apply left left', rest')
--   where 
--       (left, rest) = parseLambda (tokens)
--       (left', rest') = (parseLambda rest)
-- parseApply tokens = parseLambda tokens

-- parseMult :: [Token] -> (Expr, [Token])
-- parseMult (TMult : tokens) = (Mult e1 e2, rest')
--   where 
--     (e1, rest)  = parseExpr tokens
--     (e2, rest') = parseExpr rest
-- parseMult tokens = parseApply tokens

-- parseAdd :: [Token] -> (Expr, [Token])
-- parseAdd (TAdd : tokens) = (Add e1 e2, rest')
--   where 
--     (e1, rest)  = parseExpr tokens
--     (e2, rest') = parseExpr rest
-- parseAdd tokens = parseMult tokens

-- | 
eval :: Expr -> Value
eval = eval' Map.empty 

-- -- | 
eval' :: Map String Value -> Expr -> Value
eval' _   (Num x)                             = VInt x
eval' env (Var v)                             = env ! v
eval' env (Apply (Var v) e2)                  = case env ! v of
                                                (VFun f)  -> f (eval' env e2)
                                                _         -> error $ "expected a function, but was a variable: " ++ show v
eval' env (Apply Add e2)                      = VFun (runOp (+) (eval' env e2))
eval' env (Apply Mult e2)                     = VFun (runOp (*) (eval' env e2))
eval' env (Apply (Lambda (Var var) body) e2)  = eval' (Map.insert var (eval' env e2) env) body
eval' env (Lambda (Var var) body)             = eval' (Map.insert var (VFun $ \f -> f) env) body
eval' env (Apply e1 e2)                       = case (eval' env e1) of
                                                  (VFun f) -> f (eval' env e2)
                                                  _ -> error "Cannot apply value like a function to anothe value"
                                                  -- _ -> error $"Cannot apply value like a function to anothe value" ++ show env 
                                                  -- ++ " \n::: " ++ show e1 
                                                  -- ++ " \n::: " ++ show e2
                                                  -- ++ " \n::: " ++ show (eval' env e1)
eval' env e = error $ "Eval' error:  \n E:" ++ show e -- ++ "  " ++ show env ++ "\n"

runOp :: (Int -> Int -> Int) -> Value -> Value -> Value
runOp op e1 e2 = case (e1, e2) of 
  (VInt i, VInt j) -> VInt $ op i j
  (VFun f, VInt j) -> VFun $ \val -> runOp op (f val)  (VInt j)
  (VInt i, VFun g) -> VFun $ \val -> runOp op (VInt i) (g val) 
  (VFun f, VFun g) -> VFun $ \val -> VFun (runOp op (f val) . g)

-- ``#r #t```r t`add 1 0#f```f f f f#f#x`f`f x 
--      ===
--_r -> (  _t -> (r (t) (add (1)) (0))  ) 
--    (_f -> (f (f) (f) (f))) 
--    (_f -> (_x -> (f (f (x)))))



pp :: Expr -> String
pp (Apply e1 e2)        = pp e1 ++ " (" ++ pp e2 ++ ")"
pp (Lambda (Var v) e2)  = "_" ++ v ++ " -> (" ++ pp e2 ++ ")"
pp (Num i)              = show i
pp (Var v)              = v
pp (Add)                = "add"
pp (Mult)               = "mul"
pp _                    = "<Some invalid>"

-- Apply 
--   (Apply 
--     (Lambda 
--       (Var "r") 
--       (Lambda 
--         (Var "t") 
--           (Apply 
--             (Apply 
--               (Apply 
--                 (Var "r") 
--                 (Var "t")
--               ) 
--               (Apply 
--                 Add 
--                 (Num 1)
--               )
--             ) 
--             (Num 0)
--           )
--         )
--       ) 
--     (Lambda 
--       (Var "f") 
--       (Apply 
--         (Apply 
--           (Apply 
--             (Var "f") 
--             (Var "f")
--           ) 
--           (Var "f")
--         ) 
--         (Var "f")
--       )
--     )
--   ) 
--   (Lambda 
--     (Var "f") 
--     (Lambda 
--       (Var "x") 
--       (Apply 
--         (Var "f") 
--         (Apply 
--           (Var "f") 
--           (Var "x")
--         )
--       )
--     )
--   )

-- | 
interpret :: String -> Value
interpret  = eval . parser . lexer 
-- Apply 
--   (Lambda 
--     (Var "f") 
--     (Apply (Var "f") (Num 10))) 

--   (Lambda 
--     (Var "x") 
--     (Mult (Num 2) (Var "x")))
