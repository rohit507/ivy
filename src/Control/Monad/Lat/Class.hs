{-|
Module      : Control.Monad.Lat.Class
Description : Class for monadic construction of lattices.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Control.Monad.Lat.Class where

import Ivy.Prelude

class (Alternative m, Monad m) => MonadLat m where

  -- FIXME :: Is this really necessary? Or can we just have a
  --          well defined error type for each monad?
  type IsLatErr m e :: Constraint

  top :: (IsLatErr m e) => e -> m a
  default top :: (MonadError e m, IsLatErr m e) => e -> m a
  top = throwError

  val :: a -> m a
  default val :: (Monad m) => a -> m a
  val = pure

  bot :: m a
  default bot :: (MonadPlus m) => m a
  bot = empty
