The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE StandaloneDeriving #-}
> module Bound.Def(nf,Bound.Def.aeq,toDB,fromDB,nfd, impl, DB (..)) where
> import Lambda
> import IdInt
> import Data.Functor.Classes (Eq1(..), Show1 (..))

> import Control.Monad
> import Control.Monad.Trans.Class (lift)
> import GHC.Generics hiding (to,from)
> import Control.DeepSeq
> import Data.Monoid (All (..))
> import Control.Applicative (Const (..))
> import Debug.Trace
>
> import Bound

> import Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>            impl_name   = "Bound.Def"
>          , impl_fromLC = toDB
>          , impl_toLC   = fromDB
>          , impl_nf     = nfd
>          , impl_nfi    = error "nfi unimplemented for BoundDB"
>          , impl_aeq    = (==)
>       }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  Free variables are represented
by negative numbers.

> data DB a = DVar a | DLam (Scope () DB a) | DApp (DB a) (DB a)
>   deriving (Functor, Foldable, Traversable, Generic)

> instance NFData a => NFData (DB a)
> deriving instance Eq a => (Eq (DB a))
> deriving instance Show a => (Show (DB a))
>
> instance Eq1 DB where
>   liftEq f (DVar x) (DVar y) = f x y
>   liftEq f (DLam s1) (DLam s2) = liftEq f s1 s2
>   liftEq f (DApp a1 b1) (DApp a2 b2) = liftEq f a1 a2 && liftEq f b1 b2
>   liftEq _ _ _ = False
>
> instance Show1 DB where
>   liftShowsPrec sp _ d (DVar x) = showParen (d > 10)
>       $ showString "DVar "
>       . sp 11 x
>   liftShowsPrec sp sl d (DLam x) = showParen (d > 10)
>       $ showString "DLam "
>       . liftShowsPrec sp sl 11 x
>   liftShowsPrec sp sl d (DApp x y) = showParen (d > 10)
>       $ showString "DApp "
>       . liftShowsPrec sp sl 11 x
>       . showChar ' '
>       . liftShowsPrec sp sl 11 y

> instance Applicative DB where
>   pure = DVar
>   (<*>) = ap

> instance Monad DB where
>   return = DVar
>   DVar a   >>= f = f a
>   DApp x y >>= f = DApp (x >>= f) (y >>= f)
>   DLam x   >>= f = DLam (x >>>= f)

> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq x y = toDB x == toDB y
>

> nf :: LC IdInt -> LC IdInt
> nf = fromDB . nfd . toDB

Computing the normal form proceeds as usual.

> nfd :: DB a -> DB a
> nfd e@(DVar _) = e
> nfd (DLam e) = DLam $ toScope $ nfd $ fromScope e
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> nfd (instantiate1 a b)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form.

> whnf :: DB a -> DB a
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (instantiate1 a b)
>         f' -> DApp f' a


Convert from LC type to DB type

> toDB :: LC IdInt -> DB IdInt
> toDB = to
>   where to :: LC IdInt -> DB IdInt
>         to (Var v)   = DVar v
>         to (Lam v b) = DLam (liftingAbstract1 v (to b))
>         to (App f a) = DApp (to  f) (to a)
>

An abstract variant which lifts if variable is unused.
This is a choice. Conversion is slower, evaluation faster.

> liftingAbstract1 :: (Monad f, Traversable f, Eq a) => a -> f a -> Scope () f a
> liftingAbstract1 v t | unused    = lift t
>            | otherwise = abstract1 v t
>   where unused = getAll (getConst (traverse (\b -> Const (All (v /= b))) t))

Convert back from deBruijn to the LC type.

> fromDB :: DB IdInt -> LC IdInt
> fromDB = from firstBoundId
>   where from :: IdInt -> DB IdInt -> LC IdInt
>         from   _ (DVar v) = Var v
>         from n (DLam b)   = Lam n (from (succ n) (instantiate1 (DVar n) b))
>         from n (DApp f a) = App (from n f) (from n a)
