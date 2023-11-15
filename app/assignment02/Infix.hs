{-# OPTIONS -Wall #-}
module Infix where

import Data.Char
import Data.Bifunctor (first)


data TokenInfix
  = TNum Int
  | TPlus
  | TMult
  | TLParen
  | TRParen
  deriving (Eq, Show)
  
data Expr 
  = Num Int
  | Plus Expr Expr
  | Mult Expr Expr
  deriving (Eq, Show)

-- | Lexes Infix string into tokens
lexerInfix :: String -> [TokenInfix]
lexerInfix [] = []
lexerInfix (' ' : cs) = lexerInfix cs
lexerInfix ('+' : cs) = TPlus : lexerInfix cs
lexerInfix ('*' : cs) = TMult : lexerInfix cs
lexerInfix ('(' : cs) = TLParen : lexerInfix cs
lexerInfix (')' : cs) = TRParen : lexerInfix cs
lexerInfix cs
  | digits /= [] = TNum (read digits :: Int) : lexerInfix digitsRest
  | otherwise = error "LexerInfix: invalid input"
  where (digits, digitsRest) = span isDigit cs

-- | Parses list of tokens into an expression
-- |  Subfunctions parse in precendence of num/parens, mult, plus
parserInfix :: [TokenInfix] -> Expr
parserInfix = fst . parseAdd 
  where 
    parseExpr :: [TokenInfix] -> (Expr, [TokenInfix])
    parseExpr tokens = parseAdd tokens

    parseAdd :: [TokenInfix] -> (Expr, [TokenInfix])
    parseAdd tokens = case rest of
      (TPlus : more) -> first (Plus left) (parseAdd more)
      _              -> (left, rest)
      where (left, rest) = parseMul tokens

    parseMul :: [TokenInfix] -> (Expr, [TokenInfix])
    parseMul tokens = case rest of
      (TMult : more)  -> first (Mult left) (parseMul more)
      _               -> (left, rest)
      where (left, rest) = parseValue tokens

    parseValue :: [TokenInfix] -> (Expr, [TokenInfix])
    parseValue (TNum n : tokens) = (Num n, tokens)
    parseValue (TLParen : rest) = case tokensAfterExpr of
      (TRParen : remaining) -> (expr, remaining)
      _ -> error "Unbalanced parentheses or invalid expression"
      where (expr, tokensAfterExpr) = parseExpr rest
    parseValue _ = error "Invalid expression"

-- | Evaluate Expr
eval :: Expr -> Int
eval (Num x) = x
eval (Plus e1 e2) = eval e1 + eval e2
eval (Mult e1 e2) = eval e1 * eval e2

main :: IO()
main = do

  putStrLn "Done"