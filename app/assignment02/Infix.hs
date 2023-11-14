{-# OPTIONS -Wall #-}
module Infix where

import Data.Char

data TokenInfix = DefineYourTokenConstructorsHere
  deriving (Show)

lexerInfix :: String -> [TokenInfix]
lexerInfix = error "implement me"

data Expr = DefineYourExprConstructorsHere
  deriving (Show)

parserInfix :: [TokenInfix] -> Expr
parserInfix = error "implement me"

eval :: Expr -> Int
eval = error "implement me"