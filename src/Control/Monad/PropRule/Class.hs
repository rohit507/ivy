{-|
Module      : Control.Monad.PropRule.Class
Description : Actions that rules within a propagation network can use.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

-}

module Control.Monad.PropRule.Class where

import Ivy.Prelude
import Control.Monad.TermGraph.Class
import Control.Monad.LatMap.Class

-- | So okay, we've got, for each vertex an associated lattice term
--   for each particular lattice we are propagating information over.
--   in an ideal case
class (MonadTermGraph m, MonadLatMap v m) => MonadPropRule (v :: k) m where

  -- data Operation m :: *
  -- type Operation m = Transaction () (F (Edit m)) m

  -- | getKey and getVert define an isomorphism between vertices on the term
  --   graph and keys. getKey here should only fail when the type of v
  --   requested is incorrect.
  getKey :: (LatCons m v) => Vert m -> m (Key m v)

  getVert :: (LatCons m v) => Key m v -> Vert m
