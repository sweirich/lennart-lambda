{-# LANGUAGE RecordWildCards #-}
module Main where

import Misc
import Lambda as Lambda
import IdInt
import Impl
import Suite
import System.Exit (exitFailure)
import Control.Monad
import Test.QuickCheck

import Test.Tasty
import Test.Tasty.QuickCheck as QC 
import Test.Tasty.HUnit

prop_rt :: LambdaImpl -> LC IdInt -> Bool
prop_rt LambdaImpl{..} x = impl_toLC (impl_fromLC x) `Lambda.aeq` x

prop_aeq :: Property
prop_aeq = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
   forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \y ->
       let eq = Lambda.aeq x y in
       classify eq "aeq" $ eq == (DeBruijn.toDB x == DeBruijn.toDB y)


eqMaybe :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Property
eqMaybe f (Just x) (Just y) = classify True "aeq" (f x y)
eqMaybe _f _ _ = property True


prop_sameNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Int -> LC IdInt ->  Property
prop_sameNF f i x = eqMaybe Lambda.aeq (Simple.nfi i x) (f i x)

-- NOTE: need "fueled" version of normalization 
-- NOTE: hard to shrink and stay well-closed
prop_closedNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Property
prop_closedNF f = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
      eqMaybe Unique.aeq (DeBruijn.fromDB <$> DeBruijn.nfi 1000 (DeBruijn.toDB x)) (f 1000 x)



infixl 5 @@
(@@) :: LC IdInt -> LC IdInt -> LC IdInt
a @@ b  = App a b
lam :: Int -> LC IdInt -> LC IdInt
lam i b = Lam (IdInt i) b
var :: Int -> LC IdInt
var i   = Var (IdInt i)

lambda_false :: LC IdInt
lambda_false = lam 0 (lam 1 (var 1))


getTerm :: IO (LC Id)
getTerm = do
  contents <- readFile "timing.lam"
  return $ read (stripComments contents)
 

-- test the correctness by normalizing the benchmarking term
-- should produce result equal to false
main :: IO ()
main = do
   tm <- getTerm
   let tm1 = toIdInt tm
   let test_impl LambdaImpl{..} = do
         let result = (impl_toLC . impl_nf . impl_fromLC ) tm1 
         if Lambda.aeq lambda_false result then return ()
           else do
             putStrLn $ "FAILED: " ++ impl_name ++ " returned " ++ show result
             exitFailure
   forM_ impls test_impl



{-

-- test case that demonstrates the issue with renaming with a bound variable
-- the simplifications to t2 and t3 below do not demonstrate the bug, only t1
-- note how x3 is already in scope, 

> t1 :: LC IdInt
> t1 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>         (  (lam 1 (lam 2 (lam 3 ( var 1 @@ (lam 4 (var 4)))))) @@
>            (  (lam 1 (lam 2 ((lam 3 (var 2)) @@ (var 1 @@ var 3)))) @@
>               (lam 1 (lam 2 (var 3)))))))))


\x0.\x1.\x2.\x3.\x4.(\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.(\x3.x2) (x1 x3)) (\x1.\x2.x3))

\x0.\x1.\x2.\x3.\x4.
    (\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.(\x3.x2) (x1 x3)) (\x1.\x2.x3))
-->
    (\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.x2) (\x1.\x2.x3))

> t2 :: LC IdInt
> t2 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>         (  (lam 1 (lam 2 (lam 3 ( var 1 @@ (lam 4 (var 4)))))) @@
>            (  (lam 1 (lam 2 (var 2))) @@
>               (lam 1 (lam 2 (var 3)))))))))


\x0.\x1.\x2.\x3.\x4.\x1.\x2.(\x3.x2) (x1 x3)




> t3 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>          (lam 1 (lam 2 ((lam 3 (var 2)) @@ (var 1 @@ var 3))))))))

\x0.\x1.\x2.\x3.\x4.
   (\x1.x1 ((\x2.x1) (\x2.x2) (\x2.x2 x1))) (\x1.\x2.(\x3.\x4.x1) (\x3.x3 x2))

> t4 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>        ((lam 1 (var 1 @@ ((lam 2 (var 1)) @@ (lam 2 (var 2)) @@ (lam 2 (var 2 @@ var 1)))))
>        @@
>        (lam 1 (lam 2 ( (lam 3 (lam 4 (var 1))) @@ (lam 3 (var 3 @@ var 2))))))))))

-- Counterexample for Core

> t5 :: LC IdInt
> t5 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4 (lam 1 (lam 2 (lam 3 (lam 4 (lam 5 (var 1 @@ var 3))))))))))

-}