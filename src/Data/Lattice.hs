{-# LANGUAGE UndecidableInstances #-}

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

-- TODO :: Consider dropping bottom completely and ask the user to
--        properly use the correct bottom element w/in Lat

class (POrd l) => Lattice l where

  type LatErr (m :: * -> *) l :: Constraint
  -- latBottom :: l
  latJoin :: (MonadLat m, LatErr m l) => l -> l -> m l
  latMeet :: (MonadLat m, LatErr m l) => l -> l -> m l

class (POrdF l) => LatticeF l where

  type LatErrF (m :: * -> *) l p :: Constraint
  -- liftLatBottom :: p -> l p
  liftLatJoin   :: (MonadLat m, LatErrF m l p)
    => (p -> p -> m p) -> l p -> l p -> m (l p)
  liftLatMeet   :: (MonadLat m, LatErrF m l p)
    => (p -> p -> m p) -> l p -> l p -> m (l p)

instance (Functor l, LatticeF l, Lattice p) => Lattice (DropF l p) where

  type LatErr m (DropF l p) = (LatErrF m l p, LatErr m p)
  -- latBottom  = DF $ liftLatBottom latBottom
  latJoin (DF a) (DF b) = DF <$> liftLatJoin latJoin a b
  latMeet (DF a) (DF b) = DF <$> liftLatMeet latMeet a b

-- dropBot :: (Functor l, LatticeF l, Lattice p) => l p
-- dropBot = unDF latBottom

dropJoin :: (Functor l, LatticeF l, Lattice p, MonadLat m, LatErr m (DropF l p))
  => l p -> l p -> m (l p)
dropJoin a b = unDF <$> latJoin (DF a) (DF b)

dropMeet :: (Functor l, LatticeF l, Lattice p, MonadLat m, LatErr m (DropF l p))
  => l p -> l p -> m (l p)
dropMeet a b = unDF <$> latMeet (DF a) (DF b)
