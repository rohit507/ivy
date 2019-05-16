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

class (MonadTermGraph m) => MonadPropRule m where

  -- data Operation m :: *
  -- type Operation m = Transaction () (F (Edit m)) m

  -- | getKey and getVert define an isomorphism between vertices on the term
  --   graph and keys. getKey here should only fail when the type of v
  --   requested is incorrect.
  getKey :: forall v. (MonadLatMap v m, LatCons m v)
    => Vert m -> m (Key m v)

  getVert :: forall v. (MonadLatMap v m, LatCons m v)
    => Key m v -> Vert m
