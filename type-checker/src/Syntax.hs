module Syntax where

data Expr
    = Var String
    | Lam String Expr
    | App Expr Expr
    | If Expr Expr Expr
    | Let String Expr Expr
    | Lit Int
    | ETrue
    | EFalse
    deriving (Show, Eq)