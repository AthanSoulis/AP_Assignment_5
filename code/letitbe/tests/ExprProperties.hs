module ExprProperties where

import Test.QuickCheck

import ExprAst
import qualified ExprEval as E

--replacing Var arbitrary (and a <- arbitrary) with something like Var elements ['A'..'E']
--remedies the issue mentioned below but also reduces generality
--both versions work fine

--quality could also be further improved on by using frequency, etc.
exprN :: Int -> Gen Expr
exprN 0 = oneof [fmap Const arbitrary, fmap Var arbitrary]
exprN n = oneof 
   [fmap Const arbitrary
   , fmap Var arbitrary
   , do x <- exprN (n `div` 2)
        y <- exprN (n `div` 2)
        a <- arbitrary -- e.g. a <- vectorOf 2 (elements ['A'..'Z'])
        z <- elements [
            Oper Plus x y
            , Oper Minus x y
            , Oper Times x y
            , Let a x y] --chances of actually using a inside y are astronomically low
        return $ z       --except for Var "" which seems to be generated more often
   ]                     --which can be tested using sample $ exprN n

instance Arbitrary Expr where
   arbitrary = sized exprN

--asignment was really unspecific in what exactly was required
--the current implementation makes sense to me but involves a lot of guesswork
prop_eval_simplify :: Expr -> Property
prop_eval_simplify x = 
   -- collect (len x 0) $  (E.evalTop $ E.simplify x) === E.evalTop x 
   -- BUT:
   -- Simplify can eval expr that evalTop cant.
   -- Specifically multiplication with 0 and unused let binding
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

