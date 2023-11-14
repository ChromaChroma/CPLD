module Rpn where

import Data.Char (isDigit, isSpace)

data Token
  = TNum Int
  | TPlus
  | TMult
  deriving (Eq, Show)

data Expr
  = Num Int
  | Plus Expr Expr
  | Mult Expr Expr
  deriving (Eq, Show)

-- | Lexes RPN string into tokens
lexer :: String -> [Token]
lexer [] = []
lexer ('+' : cs) = TPlus : lexer cs
lexer ('*' : cs) = TMult : lexer cs
lexer cs
  | digits /= [] = TNum (read digits :: Int) : lexer digitsRest
  | spaces /= [] = lexer spacesRest
  | otherwise = error "invalid input"
  where
    (digits, digitsRest) = span isDigit cs
    (spaces, spacesRest) = span isSpace cs

-- | Parses the tokens
parser :: [Token] -> Expr
parser tokens = parser' [] tokens
  where
    parser' :: [Expr] -> [Token] -> Expr
    parser' [e] [] = e
    parser' [] [] = error "No expression left on stack"
    -- Numbers (Int)
    parser' (x : y : zs) [] = error "Multiple, non-combined expressions left on stack"
    parser' es (TNum x : ts) = parser' (Num x : es) ts
    -- Addition (+)
    parser' (e1 : e2 : es) (TPlus : ts) = parser' (Plus e2 e1 : es) ts
    parser' _ (TPlus : ts) = error "Invalid stack to create addition expression + "
    -- Multiplication (*)
    parser' (e1 : e2 : es) (TMult : ts) = parser' (Mult e2 e1 : es) ts
    parser' _ (TMult : ts) = error "Invalid stack to create addition expression *"
    parser'_ _ = error "Error occured: Parser could not parse tokens into an expression"

-- | Evaluate Expr
eval :: Expr -> Int
eval (Num x) = x
eval (Plus e1 e2) = eval e1 + eval e2
eval (Mult e1 e2) = eval e1 * eval e2

-- | Combines the process of lexing, parsing and evaluating an RPN string
computeRpn :: String -> Int
computeRpn = eval . parser . lexer

-- | strings of RPN arithmetic expressions
rpnExpr0, rpnExpr1, rpnExpr2, rpnExpr3, rpnExpr4 :: String
rpnExpr0 = "2 3 7 + 4 * + "
rpnExpr1 = "12 3 * 6 +"
rpnExpr2 = "1 2 3 4 5 + + + +"
rpnExpr3 = "1 2 3 4 5 + + + +"
rpnExpr4 = "123 0+2 2* +"

-- | Main test function to print all RPN expressions
main :: IO ()
main = do
  putStrLn "Start"
  print $ computeRpn rpnExpr0
  print $ computeRpn rpnExpr1
  print $ computeRpn rpnExpr2
  print $ computeRpn rpnExpr3
  print $ computeRpn rpnExpr4
  putStrLn "Done!"
