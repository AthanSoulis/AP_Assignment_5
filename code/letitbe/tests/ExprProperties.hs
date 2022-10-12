module ExprProperties where

import Test.QuickCheck

import ExprAst
import qualified ExprEval as E

exprN :: Int -> Gen Expr
exprN 0 = oneof [fmap Const arbitrary, fmap Var arbitrary]
exprN n = oneof 
   [fmap Const arbitrary
   , fmap Var arbitrary
   , do x <- exprN (n `div` 2)
        y <- exprN (n `div` 2)
        a <- arbitrary
        z <- elements [
            Oper Plus x y
            , Oper Minus x y
            , Oper Times x y
            , Let a x y] --chances of actually using a inside y are astronomically low
        return $ z
   ]

instance Arbitrary Expr where
   arbitrary = sized exprN

prop_eval_simplify :: Expr -> Property
prop_eval_simplify x = --E.evalTop x === (E.evalTop $ E.simplify x) but:
   --simplify can eval expr that evalTop cant
   --specifically multiplication with 0 and unused let binding
   let simp = (E.simplify x) in let res = (E.evalTop x) in case res of
         Left _ -> True === True --no way to check this
         Right _ -> E.evalTop simp === res