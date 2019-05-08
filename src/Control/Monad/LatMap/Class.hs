{-|
Module      : Control.Monad.LatMap.Class
Description : Class for monadic key-value stores, where the values are
              lattice elements unified with the join operator.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Control.Monad.LatMap.Class where

import Ivy.Prelude

class (Monad m) => MonadLatMap (v :: k) (m :: * -> *) where

  data Key     m v :: *
  data LatMemb m v :: *
  type LatCons m v :: Constraint

  putLat   :: (LatCons m v) => LatMemb m v -> m (Key m v)

  getLat   :: (LatCons m v) => Key m v -> m (LatMemb m v)

  bindLat  :: (LatCons m v) => Key m v -> LatMemb m v -> m (Key m v)

  equals   :: (LatCons m v) => Key m v -> Key  m v -> m (Key m v)

  subsumes :: (LatCons m v) => Key m v -> Key  m v -> m Bool
