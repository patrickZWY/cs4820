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
