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

substLookup :: Natural -> Subst -> Maybe Ty
substLookup n (Subst s) = lookup n s

envLookup :: String -> TyEnv -> Maybe Ty
envLookup name (TyEnv env) = lookup name env

applySubstTy :: Subst -> Ty -> Ty
applySubstTy subst ty = case ty of
    TBool -> TBool
    TVar n -> case substLookup n subst of
        Just ty' -> ty'
        Nothing -> ty
    TFun ty1 ty2 -> mkTFun (applySubstTy subst ty1) (applySubstTy subst ty2)

--update typing environment recursively with substitution
applySubstEnv :: Subst -> TyEnv -> TyEnv
applySubstEnv subst (TyEnv env) = TyEnv [(name, applySubstTy subst ty) | (name, ty) <- env]

occursInTy :: Natural -> Ty -> Bool
occursInTy n ty = case ty of
    TBool -> False
    TVar m -> n == m
    TFun ty1 ty2 -> occursInTy n ty1 || occursInTy n ty2

substHasKey :: Natural -> Subst -> Bool
substHasKey n (Subst s) = any (\(m, _) -> m == n) s

composeSubstAux :: Subst -> Subst -> Subst
composeSubstAux (Subst s1) (Subst s2) =
    Subst (go s1)
    where
        go [] = []
        go ((k, ty) : rest)
            | substHasKey k (Subst s2) = go rest
            | otherwise = (k, applySubstTy (Subst s2) ty) : go rest

composeSubst :: Subst -> Subst -> Subst
composeSubst s1@(Subst _) s2@(Subst raw2) =
    let Subst filtered = composeSubstAux s1 s2
    in Subst (filtered ++ raw2)

data UnifyResult
    = UnifyOk Subst
    | UnifyFail String
    deriving (Show, Eq)

-- no checking if substp because data type already enforced by Haskell
unifyOkp :: UnifyResult -> Bool
unifyOkp (UnifyOk _) = True
unifyOkp _ = False

-- this is not needed because we can pattern match on the UnifyResult
{-
unifysubst :: unifyresult -> subst
unifysubst (unifyok subst) = subst
unifysubst _ = error "unification failed, no substitution available"
-}

-- again we do not need to tag a ok or fail because our haskell data type

bindTVar :: Natural -> Ty -> UnifyResult
bindTVar n ty
    | ty == mkTVar n = UnifyOk (Subst [])
    | occursInTy n ty = UnifyFail ("Occurs check failed: cannot unify " 
        ++ show (mkTVar n) ++ " with " ++ show ty)
    | otherwise = UnifyOk (Subst [(n, ty)])


unify :: Ty -> Ty -> UnifyResult
unify ty1 ty2 = case (ty1, ty2) of
    (TBool, TBool) -> UnifyOk (Subst [])

    (TVar n, ty) -> bindTVar n ty
    (ty, TVar n) -> bindTVar n ty

    (TFun dom1 cod1, TFun dom2 cod2) ->
        case unify dom1 dom2 of
            UnifyFail msg ->
                UnifyFail $
                    "Failed to unify function domains: "
                    ++ show dom1 ++ " and " ++ show dom2
                    ++ ". Reason: " ++ msg

            UnifyOk subst1 ->
                case unify (applySubstTy subst1 cod1)
                            (applySubstTy subst1 cod2) of
                    UnifyFail msg ->
                        UnifyFail $
                            "Failed to unify function codomains: "
                            ++ show cod1 ++ " and " ++ show cod2
                            ++ ". Reason: " ++ msg

                    UnifyOk subst2 ->
                        UnifyOk (composeSubst subst2 subst1)

    _ ->
        UnifyFail $
            "Failed to unify types: "
            ++ show ty1 ++ " and " ++ show ty2









