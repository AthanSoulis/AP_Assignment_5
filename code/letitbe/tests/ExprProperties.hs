module ExprProperties where

import Test.QuickCheck

import ExprAst
import qualified ExprEval as E

import Data.Either

exprN :: Int -> Gen Expr
exprN 0 = oneof [fmap Const arbitrary, fmap Var $ vectorOf 5 $ elements ['A'..'Z']]
exprN n = oneof 
   [fmap Const arbitrary
   , fmap Var $ vectorOf 5 $ elements ['A'..'Z']
   , do x <- exprN (n `div` 2)
        y <- exprN (n `div` 2)
        a <- vectorOf 5 $ elements ['A'..'Z']
        z <- elements [
         Oper Plus x y
         , Oper Minus x y
         , Oper Times x y
         , Let a x y] --chances of actually using a inside y are astronomically low
        return $ z
   ]

data UpperCaseString = UpperCaseString String

instance Arbitrary UpperCaseString where
   arbitrary = do
      n <- chooseInt (0, 5)
      str <- vectorOf n (elements ['A'..'Z'])
      return $ UpperCaseString str

instance Arbitrary Expr where
   arbitrary = sized exprN

prop_eval_simplify :: Expr -> Property
prop_eval_simplify x = --E.evalTop x === (E.evalTop $ E.simplify x)
   let simp = (E.simplify x) in let res = (E.evalTop x) in case simp of
   (Const 0) -> True === True                   -- evalTop can be whatever, including Left _
   _         -> case res of
                  Left _ ->  (isLeft $ E.evalTop simp) === True
                  Right _ -> E.evalTop x === (E.evalTop simp)