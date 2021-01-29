-- The DeBruijn module implements the Normal Form function by
-- using de Bruijn indicies.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wall #-}
-- | This is normalisation by evaluation inspired
-- evaluator.
--
--
module Impl.BoundNbE (nf,Impl.BoundDB.aeq,toDB,fromDB,nfd, impl) where

import Lambda
import IdInt

import Bound
import Control.Monad.Trans.Class (lift)
import Impl.BoundDB (DB (..), fromDB, toDB, aeq)

import Impl

impl :: LambdaImpl
impl = LambdaImpl {
           impl_name   = "BoundNbE"
         , impl_fromLC = toDB
         , impl_toLC   = fromDB
         , impl_nf     = nfd
         , impl_nfi    = error "nfi unimplemented for BoundNbE"
         , impl_aeq    = (==)
      }

-- Semantic values are either
-- 1. Done
-- 2. Closures which don't wait for a value.
-- 3. Or do.
--
data Sem b where
    Done :: DB b                                   -> Sem b
    Skip :: Sem b                                  -> Sem b
    Clos :: (forall a. (b -> a) -> Sem a -> Sem a) -> Sem b

instance Functor Sem where
    fmap f (Done d) = Done (fmap f d)
    fmap f (Skip g) = Skip (fmap f g)
    fmap f (Clos g) = Clos $ \ren sem -> g (ren . f) sem

-- | Semantic environments
data Env a b where
    Nil  :: (a -> b) -> Env a b
    Ext :: Env a b -> Sem b -> Env (Var () a) b

instance Functor (Env a) where
    fmap f (Nil g)       = Nil (f . g)
    fmap f (Ext env sem) = Ext (fmap f env) (fmap f sem) 

-- Lookup semantic value in semantic environment.
look :: Env a b -> a -> Sem b
look (Nil f) a              = Done (DVar (f a))
look (Ext env _)   (F x)    = look env x
look (Ext _   sem) (B ~())  = sem

-- Lowering semantic values to concrete syntax.
-- 1. Done is trivial.
-- 2. Skip we can efficiently lift
-- 3. Otherwise we build a lambda in "ordinary" NbE approach.
--
lower :: Sem a -> DB a
lower (Done x) = x
lower (Skip f) = DLam $ lift $ lower f
lower (Clos f) = DLam $ toScope $ lower $ f F (Done (DVar (B ())))

nf :: LC IdInt -> LC IdInt
nf = fromDB . nfd . toDB

eval2 :: Env a b -> DB a -> Sem b
eval2 env (DVar x) = look env x

-- Function application has three cases
-- 1. When head is done, lower.eval the argument
-- 2. If skip, we don't need argument
-- 3. Otherwise apply closure.
--
eval2 env (DApp f t) = case eval2 env f of
    Done f' -> Done (DApp f' (lower t'))
    Skip f' -> f'
    Clos g  -> g id t'
  where
    t' = eval2 env t

-- In lambda abstraction we recognise Scoped (DVar ..) case
-- 1. it's either a lift, then we make a Skip semantic value.
-- 2. or it is an identity, then we use t
-- Otherwise we fallback to "ordinary" NbE encoding
--
eval2 env (DLam (Scope (DVar (F b)))) = Skip $
    eval2 env b
eval2 env (DLam (Scope (DVar (B x)))) = Clos $ \_ren t ->
    t
eval2 env (DLam b) = Clos $ \ren t ->
    eval2 (Ext (fmap ren env) t) (fromScope b)

nfd :: DB a -> DB a
nfd = lower . eval2 (Nil id)
