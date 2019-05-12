{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : Control.Monad.Prop.Class
Description : Class for monads which can describe a propagation network.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

-}

module Control.Monad.Prop.Class where

import Ivy.Prelude
import Control.Monad.TermGraph.Class
import Control.Monad.LatMap.Class
import Data.Transaction

class (MonadTermGraph m) => MonadTermLat m where

  -- data Operation m :: *
  -- type Operation m = Transaction () (F (Edit m)) m

  -- | getKey and getVert define an isomorphism between vertices on the term
  --   graph and keys. getKey here should only fail when the type of v
  --   requested is incorrect.
  getKey :: forall v. (MonadLatMap v m, LatCons m v)
    => Vert m -> m (Key m v)

  getVert :: forall v. (MonadLatMap v m, LatCons m v)
    => Key m v -> Vert m

class (MonadTermLat m) => MonadProp m where

  -- | Will run all rules until there are no more to run.
  quiesce :: m ()

  -- | The first three parameters carry proofs that you can use certain
  --   features of m' in m.
  --   The fourth is a morphism from m to m' letting you basically lift
  --   actions from one into the other.
  --
  --   Yeah this model is a bit kludgy but it should do for now.
  --   Alternately we could just have this work on m, but then we wouldn't be
  --   able to insert our, oh so important, transaction management layer.
  --
  --   Whatever, it'll do for now.
  --
  --   TODO :: Find better way to do this, maybe consolidate constraint
  --           dicts into a single newtype.
  addRule :: forall t. (TermCons t m)
    => (Term t m -> TransactT s m ()) -> m ()
