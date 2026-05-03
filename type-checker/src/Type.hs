module Type where
import GHC.Natural (Natural, naturalFromInteger)
import Syntax (Expr(..))
import GHC.TypeLits (Nat)

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

data InferResult
    = InferOk Subst Ty Natural
    | InferFail String
    deriving (Show, Eq)

-- inferSubst :: InferResult -> Subst
-- inferSubst (InferOk subst _ _) = subst
-- inferSubst _ = error "Inference failed, no substitution available"

-- inferType :: InferResult -> Ty
-- inferType (InferOk _ ty _) = ty
-- inferType _ = error "Inference failed, no type available"

-- inferNext :: InferResult -> Natural
-- inferNext (InferOk _ _ next) = next
-- inferNext _ = error "Inference failed, no next type variable available"

freshTyVar :: Natural -> (Ty, Natural)
freshTyVar next = (TVar next, next + 1)

envExtend :: String -> Ty -> TyEnv -> TyEnv
envExtend name ty (TyEnv env) = TyEnv ((name, ty) : env)

inferTrue :: TyEnv -> Expr -> Natural -> InferResult
inferTrue _ ETrue next = InferOk (Subst []) TBool next
inferTrue _ _ _ = InferFail "Expected ETrue expression"

inferFalse :: TyEnv -> Expr -> Natural -> InferResult
inferFalse _ EFalse next = InferOk (Subst []) TBool next
inferFalse _ _ _ = InferFail "Expected EFalse expression"

inferVar :: TyEnv -> Expr -> Natural -> InferResult
inferVar env (Var name) next = case envLookup name env of
    Just ty -> InferOk (Subst []) ty next
    Nothing -> InferFail ("Unbound variable: " ++ name)
inferVar _ _ _ = InferFail "Expected Var expression"

inferLam :: TyEnv -> Expr -> Natural -> InferResult
inferLam env (Lam var body) next =
    let (paramTy, next1) = freshTyVar next
        env' = envExtend var paramTy env
    in case infer env' body next1 of
        InferFail msg -> InferFail ("Failed to infer lambda body: " ++ msg)
        InferOk subst bodyTy next2 ->
            -- param needs to be updated with the substitution because it
            -- may contain type variables that were unified during the inference of the body 
            let funTy = mkTFun (applySubstTy subst paramTy) bodyTy
            in InferOk subst funTy next2
inferLam _ _ _ = InferFail "Expected Lam expression"  

inferApp :: TyEnv -> Expr -> Natural -> InferResult
inferApp env (App fun arg) next =
    case infer env fun next of
        InferFail msg -> InferFail ("Failed to infer function: " ++ msg)
        InferOk substFun funTy next1 ->
            case infer (applySubstEnv substFun env) arg next1 of
                InferFail msg -> InferFail ("Failed to infer argument: " ++ msg)
                InferOk substArg argTy next2 ->
                    let tmp = freshTyVar next2
                        (resultTy, next3) = tmp
                        -- this is the type we construct for the function with unknown result type
                        funTyExpected = mkTFun argTy resultTy
                    -- unify it with the inferred body type of the function (updated by substitution)
                    in case unify (applySubstTy substArg funTy) funTyExpected of
                        UnifyFail msg -> InferFail ("Failed to unify function type: " ++ msg)
                        UnifyOk substUnify ->
                            -- substUnify is the latest substitution
                            let subst = composeSubst substUnify (composeSubst substArg substFun)
                            in InferOk subst resultTy next3
inferApp _ _ _ = InferFail "Expected App expression"       


inferIf :: TyEnv -> Expr -> Natural -> InferResult
inferIf env (If cond thenBranch elseBranch) next =
    case infer env cond next of
        InferFail msg -> InferFail ("Failed to infer condition: " ++ msg)
        InferOk substCond condTy next1 ->
            case unify condTy TBool of
                UnifyFail msg -> InferFail ("Condition must be of type Bool: " ++ msg
                    ++ " Inferred type: " ++ show condTy)
                UnifyOk substUnifyCond ->
                    let subst1 = composeSubst substUnifyCond substCond 
                    in case infer (applySubstEnv subst1 env) thenBranch next1 of
                        InferFail msg -> InferFail ("Failed to infer then branch: " ++ msg)
                        InferOk substThen thenTy next2 ->
                            case infer (applySubstEnv substThen (applySubstEnv subst1 env)) elseBranch next2 of
                                InferFail msg -> InferFail ("Failed to infer else branch: " ++ msg)
                                InferOk substElse elseTy next3 ->
                                    case unify (applySubstTy substElse thenTy) elseTy of
                                        UnifyFail msg -> InferFail ("Then and Else branch must be of same type: " ++ msg
                                            ++ " Then branch: " ++ show (applySubstTy substElse thenTy) ++ " Else branch: "
                                            ++ show elseTy)
                                        UnifyOk substUnifyElse ->
                                            let s = foldr1 composeSubst [substUnifyElse, substElse, substThen, substUnifyCond, substCond]
                                                in InferOk s (applySubstTy s elseTy) next
inferIf _ _ _ = InferFail "Unexpected If expression"

infer :: TyEnv -> Expr -> Natural -> InferResult
infer env expr next = case expr of
    ETrue -> inferTrue env expr next
    EFalse -> inferFalse env expr next
    Var _ -> inferVar env expr next
    Lam _ _ -> inferLam env expr next
    App _ _ -> inferApp env expr next
    If {} -> inferIf env expr next
















