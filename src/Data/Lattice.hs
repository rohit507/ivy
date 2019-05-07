{-|
Module      : Data.Lattice
Description : Class of partially ordered values with meet and join
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Data.Lattice where

import Ivy.Prelude
import Data.POrd
import Control.Monad.Lat.Class

class (POrd l) => Lattice l where
  latBottom :: l
  latJoin :: (MonadLat m) => l -> l -> m l
  latMeet :: (MonadLat m) => l -> l -> m l


class (POrdF l) => LatticeF l where
  liftLatBottom :: p -> l p
  liftLatJoin   :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m (l p)
  liftLatMeet   :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m (l p)

class (Functor (l k)) => LatticeKF k l where

  liftLatBottomWithKey :: p -> l k p
  liftLatJoinWithKey :: (MonadLat m) => (p -> p -> m p) -> l k p -> l k p -> m (l k p)
  liftLatMeetWithKey :: (MonadLat m) => (p -> p -> m p) -> l k p -> l k p -> m (l k p)
