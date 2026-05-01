module Type where
import GHC.Natural (Natural)
import Syntax (Expr(..))

data Ty
    = TVar Natural
    | TFun Ty Ty
    | TBool
    deriving (Show, Eq)

newtype TyEnv = TyEnv [(String, Ty)]
    deriving (Show, Eq)

newtype Subst = Subst [(Natural, Ty)]
    deriving (Show, Eq)

tyTag :: Ty -> String
tyTag ty = case ty of
    TVar _ -> "TVar"
    TFun _ _ -> "TFun"
    TBool -> "TBool"

tVarId :: Ty -> Maybe Natural
tVarId ty = case ty of
    TVar n -> Just n
    _ -> Nothing

funDom :: Ty -> Maybe Ty
funDom ty = case ty of
    TFun dom _ -> Just dom
    _ -> Nothing

funCod :: Ty -> Maybe Ty
funCod ty = case ty of
    TFun _ cod -> Just cod
    _ -> Nothing

mkTVar :: Natural -> Ty
mkTVar n = TVar n

mkTFun :: Ty -> Ty -> Ty
mkTFun dom cod = TFun dom cod

exprTag :: Expr -> String
exprTag expr = case expr of
    ETrue -> "ETrue"
    EFalse -> "EFalse"
    Var _ -> "Var"
    Lam _ _ -> "Lam"
    App _ _ -> "App"
    If _ _ _ -> "If"

varName :: Expr -> String
varName expr = case expr of
    Var name -> name
    _ -> error "Not a Var expression"

lamVar :: Expr -> String
lamVar expr = case expr of
    Lam var _ -> var
    _ -> error "Not a Lam expression"

lamBody :: Expr -> Expr
lamBody expr = case expr of
    Lam _ body -> body
    _ -> error "Not a Lam expression"

appFun :: Expr -> Expr
appFun expr = case expr of
    App fun _ -> fun
    _ -> error "Not an App expression"

appArg :: Expr -> Expr
appArg expr = case expr of
    App _ arg -> arg
    _ -> error "Not an App expression"

ifCond :: Expr -> Expr
ifCond expr = case expr of
    If cond _ _ -> cond
    _ -> error "Not an If expression"

ifThen :: Expr -> Expr
ifThen expr = case expr of
    If _ thenBranch _ -> thenBranch
    _ -> error "Not an If expression"

ifElse :: Expr -> Expr
ifElse expr = case expr of
    If _ _ elseBranch -> elseBranch
    _ -> error "Not an If expression"


