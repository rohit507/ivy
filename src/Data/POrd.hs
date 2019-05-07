{-|
Module      : Data.POrd
Description : Class of values with a partial ordering.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Data.POrd where

import Ivy.Prelude

class POrd l where

  lessThanOrEq    :: l -> l -> Bool
  lessThan        :: l -> l -> Bool
  greaterThanOrEq :: l -> l -> Bool
  greaterThan     :: l -> l -> Bool
  equalTo         :: l -> l -> Bool
  notEqualTo      :: l -> l -> Bool

class (Functor l) => POrdF l where

  liftLessThanOrEq    :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftLessThan        :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftGreaterThanOrEq :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftGreaterThan     :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftEqualTo         :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftNotEqualTo      :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool

newtype DropF l p = DF { unDF :: l p }

instance (Functor l, POrdF l, POrd p) => POrd (DropF l p) where

  lessThanOrEq (DF a) (DF b)
    = runIdentity $ liftLessThanOrEq (\ x y -> pure $ lessThanOrEq x y) a b
  lessThan (DF a) (DF b)
    = runIdentity $ liftLessThan     (\ x y -> pure $ lessThan     x y) a b

  greaterThanOrEq (DF a) (DF b)
    = runIdentity $ liftGreaterThanOrEq (\ x y -> pure $ greaterThanOrEq x y) a b
  greaterThan (DF a) (DF b)
    = runIdentity $ liftGreaterThan     (\ x y -> pure $ greaterThan    x y) a b

  equalTo (DF a) (DF b)
    = runIdentity $ liftEqualTo (\ x y -> pure $ equalTo x y) a b
  notEqualTo (DF a) (DF b)
    = runIdentity $ liftNotEqualTo (\ x y -> pure $ notEqualTo x y) a b

dropLTE :: (Functor l, POrdF l, POrd p) => l p -> l p -> Bool
dropLTE a b = lessThanOrEq (DF a) (DF b)
dropLT :: (Functor l, POrdF l, POrd p) => l p -> l p -> Bool
dropLT a b = lessThan (DF a) (DF b)
dropGTE :: (Functor l, POrdF l, POrd p) => l p -> l p -> Bool
dropGTE a b = greaterThanOrEq (DF a) (DF b)
dropGT :: (Functor l, POrdF l, POrd p) => l p -> l p -> Bool
dropGT a b = greaterThan (DF a) (DF b)
dropEQ :: (Functor l, POrdF l, POrd p) => l p -> l p -> Bool
dropEQ a b = equalTo (DF a) (DF b)
dropNEQ :: (Functor l, POrdF l, POrd p) => l p -> l p -> Bool
dropNEQ a b = notEqualTo (DF a) (DF b)
