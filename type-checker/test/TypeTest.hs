module TypeTest where

import Test.Hspec
import Type
import Syntax

spec :: Spec
spec = do
    describe "Ty helpers" $ do
        it "gets TVar id" $ do
            tVarId (TVar 3) `shouldBe` Just 3
        
        it "returns Nothing when tVarId is used on TFun" $ do
            tVarId (TFun (TVar 0) (TVar 1)) `shouldBe` Nothing

        it "gets function domain" $ do
            funDom (TFun (TVar 0) (TVar 1)) `shouldBe` Just (TVar 0)
        
        it "gets function codomain" $ do
            funCod (TFun (TVar 0) (TVar 1)) `shouldBe` Just (TVar 1)
        
    describe "Subst" $ do
        it "checks if a substitution has a key" $ do
            substHasKey 3 (Subst [(3, TBool), (4, TVar 0)]) `shouldBe` True
        
        it "checks if a substitution does not have a key" $ do
            substHasKey 5 (Subst [(3, TBool), (4, TVar 0)]) `shouldBe` False

        it "checks if a substitution has a key when the substitution is empty" $ do
            substHasKey 3 (Subst []) `shouldBe` False
        
        it "applies substitution to a matching TVar" $ do
            applySubstTy (Subst [(0, TBool)]) (TVar 0) `shouldBe` TBool
        
        it "leaves unmatched TVar unchanged" $ do
            applySubstTy (Subst [(0, TBool)]) (TVar 1) `shouldBe` TVar 1
        
        it "applies substitution to a TFun" $ do
            applySubstTy (Subst [(0, TBool)]) (TFun (TVar 0) (TVar 1)) `shouldBe` TFun TBool (TVar 1)

        it "composes substitutions correctly" $ do
            let s1 = Subst [(1, TVar 0)]
            let s2 = Subst [(0, TBool)]
            composeSubst s1 s2 `shouldBe` Subst [(1, TBool), (0, TBool)]

        it "composes respects application order" $ do
            let s1 = Subst [(1, TVar 0)]
            let s2 = Subst [(0, TBool)]
            applySubstTy (composeSubst s1 s2) (TVar 1)
                `shouldBe`
                applySubstTy s2 (applySubstTy s1 (TVar 1))

        it "applying empty substitution does nothing" $ do
            applySubstTy (Subst []) (TFun (TVar 0) (TVar 1))
                `shouldBe`
                TFun (TVar 0) (TVar 1)

        it "applies substitution recursively" $ do
            applySubstTy
                (Subst [(0, TFun TBool (TVar 1))])
                (TVar 0)
                `shouldBe`
                TFun TBool (TVar 1)
    
    describe "unify" $ do
        it "unifies two identical TBool types" $ do
            unify TBool TBool `shouldBe` UnifyOk (Subst [])
        
        it "unifies a TVar with a type" $ do
            unify (TVar 0) TBool `shouldBe` UnifyOk (Subst [(0, TBool)])
        
        it "fails to unify a TVar with a type that contains itself" $ do
            unify (TVar 0) (TFun (TVar 0) TBool) `shouldBe`
                UnifyFail "Occurs check failed: cannot unify TVar 0 with TFun (TVar 0) TBool"

    describe "infer-top" $ do
        it "infers id" $ do
            inferTopType (Lam "x" (Var "x")) `shouldBe` Just (TFun (TVar 0) (TVar 0))
        it "infers α -> Bool" $ do
            inferTopType (Lam "x" ETrue) `shouldBe` Just (TFun (TVar 0) TBool)
        it "infers α -> Bool2" $ do
            inferTopType (Lam "x" EFalse) `shouldBe` Just (TFun (TVar 0) TBool)
        it "infers K-Combinator α -> β -> α" $ do
            inferTopType (Lam "x" (Lam "y" (Var "x"))) `shouldBe` Just (TFun (TVar 0) (TFun (TVar 1) (TVar 0)))
        it "infers α -> β -> β" $ do
            inferTopType (Lam "x" (Lam "y" (Var "y"))) `shouldBe` Just (TFun (TVar 0) (TFun (TVar 1) (TVar 1)))
        it "infers Bool" $ do
            inferTopType (App (Lam "x" (Var "x")) ETrue) `shouldBe` Just TBool
        it "infers Bool2" $ do
            inferTopType (App (App (Lam "x" (Lam "y" (Var "x"))) ETrue) EFalse) `shouldBe` Just TBool
        it "infers Bool3" $ do
            inferTopType (If ETrue EFalse ETrue) `shouldBe` Just TBool
        it "infers Bool4" $ do
            inferTopType (If EFalse ETrue EFalse) `shouldBe` Just TBool
        it "infers Bool -> Bool" $ do
            inferTopType (Lam "x" (If (Var "x") ETrue EFalse)) `shouldBe` Just (TFun TBool TBool)
        it "infers Bool -> Bool" $ do
            inferTopType (Lam "x" (If (Var "x") (Var "x") EFalse)) `shouldBe` Just (TFun TBool TBool)
        it "infers Bool -> Bool -> Bool" $ do
            inferTopType (Lam "x" (Lam "y" (If (Var "x") (Var "y") ETrue))) `shouldBe` Just (TFun TBool (TFun TBool TBool))
        it "infers α -> α" $ do
            inferTopType (Lam "f" (Var "f")) `shouldBe` Just (TFun (TVar 0) (TVar 0))
        it "infers α -> α2" $ do
            inferTopType (App (Lam "f" (Lam "x" (App (Var "f") (Var "x")))) (Lam "z" (Var "z"))) `shouldBe` 
                Just (TFun (TVar 0) (TVar 0))
        it "infers (α -> β) -> α -> β" $ do
            inferTopType (Lam "f" (Lam "x" (App (Var "f") (Var "x")))) `shouldBe`
                Just (TFun (TFun (TVar 0) (TVar 1)) (TFun (TVar 0) (TVar 1)))

        it "infers B-Combinator (δ -> σ) -> (α -> δ) -> (α -> σ)" $ do
            inferTopType (Lam "f" (Lam "g" (Lam "x" (App (Var "f") (App (Var "g") (Var "x"))))))
                `shouldBe` Just (TFun (TFun (TVar 0) (TVar 1)) (TFun (TFun (TVar 2) (TVar 0)) (TFun (TVar 2) (TVar 1))))

        it "infers (Bool -> α) -> α" $ do 
            inferTopType (Lam "f" (App (Var "f") ETrue)) `shouldBe`
                Just (TFun (TFun TBool (TVar 0)) (TVar 0))
        
        it "infers (Bool -> α) -> β -> α" $ do
            inferTopType (Lam "f" (Lam "x" (App (Var "f") ETrue))) `shouldBe`
                Just (TFun (TFun TBool (TVar 0)) (TFun (TVar 1) (TVar 0)))
        
        it "infers (α -> β) -> α -> β" $ do
            inferTopType (Lam "f" (Lam "x" (App (Var "f") (Var "x")))) `shouldBe`
                Just (TFun (TFun (TVar 0) (TVar 1)) (TFun (TVar 0) (TVar 1)))

        it "infers C-Combinator (α -> β -> γ) -> β -> α -> γ" $ do 
            inferTopType (Lam "f" (Lam "x" (Lam "y" (App (App (Var "f") (Var "y")) (Var "x")))))
                `shouldBe` Just (TFun (TFun (TVar 0) (TFun (TVar 1) (TVar 2))) (TFun (TVar 1) (TFun (TVar 0) (TVar 2))))

        it "infers W-Combinator (α -> α -> β) -> α -> β" $ do
            inferTopType (Lam "f" (Lam "x" (App (App (Var "f") (Var "x")) (Var "x"))))
                `shouldBe` Just (TFun (TFun (TVar 0) (TFun (TVar 0) (TVar 1))) (TFun (TVar 0) (TVar 1)))

        it "infers S-Combinator (α -> (ε -> κ)) -> (α -> ε) -> (α -> κ)" $ do
            inferTopType (Lam "f" (Lam "g" (Lam "x" (App (App (Var "f") (Var "x")) (App (Var "g") (Var "x"))))))
                `shouldBe` Just (TFun (TFun (TVar 0) (TFun (TVar 1) (TVar 2))) (TFun (TFun (TVar 0) (TVar 1)) (TFun (TVar 0) (TVar 2))))

    describe "infer error cases" $ do
        it "fails on unbound variable" $ do
            inferTopType (Var "x") `shouldBe` Nothing
            inferTopType (Lam "x" (Var "y")) `shouldBe` Nothing

        it "fails when applying a non-function" $ do
            inferTopType (App ETrue EFalse) `shouldBe` Nothing
            inferTopType (Lam "x" (App ETrue (Var "x"))) `shouldBe` Nothing

        it "fails on heterogeneous if branches" $ do
            inferTopType (If ETrue EFalse (Lam "x" ETrue)) `shouldBe` Nothing
            inferTopType (If ETrue (Lam "x" ETrue) EFalse) `shouldBe` Nothing

        it "fails on bad if condition" $ do
            inferTopType (If (Lam "x" ETrue) EFalse ETrue) `shouldBe` Nothing

        it "fails on occurs check" $ do
            inferTopType (Lam "x" (App (Var "x") (Var "x"))) `shouldBe` Nothing
            inferTopType (Lam "f" (Lam "x" (App (Var "f") (Var "f"))))
                `shouldBe` Nothing


        

