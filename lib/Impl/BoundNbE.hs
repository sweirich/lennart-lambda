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

-- Semantic values.
data Sem b where
    Done :: DB b                                   -> Sem b
    -- three ways to represent lambdas.
    -- 1. a value which doesn't use binding
    -- 2. a closure
    -- 3. a Hoas (which we don't use, but could for primitive operations).
    --
    Skip :: Sem b                                  -> Sem b
    Clos :: Closure b                              -> Sem b
    Hoas :: (forall a. (b -> a) -> Sem a -> Sem a) -> Sem b

-- This is used often.
var0 :: Sem (Var () a)
var0 = Done (DVar (B ()))

instance Functor Sem where
    fmap f (Done d) = Done (fmap f d)
    fmap f (Skip g) = Skip (fmap f g)
    fmap f (Clos c) = Clos (fmap f c)
    fmap f (Hoas g) = Hoas $ \ren sem -> g (ren . f) sem

-- | Closure of environment and a (lambda) body.
data Closure a where
    Closure :: Env a b -> DB (Var () a) -> Closure b

instance Functor Closure where
    fmap f (Closure env d) = Closure (fmap f env) d

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
-- 3. Closures are converted to scope by instantiting them,
--    and then lowering that.
-- 4. Otherwise we build a lambda in "ordinary" NbE approach.
--
lower :: Sem a -> DB a
lower (Done x)     = x
lower (Skip f)     = DLam $ lift $ lower f
lower (Clos c)     = DLam $ closureToScope c
lower (Hoas f)     = DLam $ toScope $ lower $ f F var0

closureToScope :: Closure a -> Scope () DB a
closureToScope (Closure env d) = toScope $ lower $ eval (Ext (fmap F env) var0) d

nf :: LC IdInt -> LC IdInt
nf = fromDB . nfd . toDB

-- instantiation of closure
inst :: Closure b -> Sem b -> Sem b
inst (Closure env f) x = eval (Ext env x) f

-- Function application has four cases
-- 1. When head is done, lower.eval the argument
-- 2. If skip, we don't need argument
-- 3. If closure, instantiate
-- 4. Otherwise apply closure.
--
app :: Sem a -> Sem a -> Sem a
app f t = case f of
    Done f' -> Done (DApp f' (lower t))
    Skip f' -> f'
    Clos c  -> inst c t
    Hoas g  -> g id t

eval :: Env a b -> DB a -> Sem b
eval env (DVar x)                    = look env x
eval env (DApp f t)                  = app (eval env f) (eval env t)
-- In lambda abstraction we recognise Scoped (DVar ..) case
-- If it's a lift, we make a Skip value
-- Otherwise we fallback to making a closure.
--
eval env (DLam (Scope (DVar (F b)))) = Skip $ eval env b
eval env (DLam b)                    = Clos (Closure env (fromScope b))

nfd :: DB a -> DB a
nfd = lower . eval (Nil id)
