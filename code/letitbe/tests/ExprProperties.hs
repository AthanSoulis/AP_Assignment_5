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
   collect (len x 0) $
   let simp = (E.simplify x) in let res = (E.evalTop x) in case res of
            Left _ -> True === True --no way to check this
            Right _ -> E.evalTop simp === res

--determines the "length" of an expression
len x n = case x of
   Const _ -> n + 1
   Var _   -> n + 1
   Oper _ e1 e2 ->  n + 1 + len e1 0 + len e2 0
   Let _ e1 e2 -> n + 1 + len e1 0 + len e2 0

