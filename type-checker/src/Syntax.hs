module Syntax where

data Expr
    = Var String
    | Lam String Expr
    | App Expr Expr
    | If Expr Expr Expr
    | ETrue
    | EFalse
    deriving (Show, Eq)