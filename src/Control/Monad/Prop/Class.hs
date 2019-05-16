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

-- | FIXME :: Do we even want this, instead of just treating a propagation
--   network as a single (Pure-ish) value?
class (Monad m) => MonadProp m where

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
    => (Term t m -> Transaction m ()) -> m ()
