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
