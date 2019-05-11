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

class (MonadTermGraph m) => MonadProp m where

  data Operation m :: *
  -- type Operation m = Transaction () (F (Edit m)) m

  -- | getKey and getVert define an isomorphism between vertices on the term
  --   graph and keys. getKey here should only fail when the type of v
  --   requested is incorrect.
  getKey :: forall v. (MonadLatMap v m, LatCons m v)
    => Vert m -> m (Key m v)

  getVert :: forall v. (MonadLatMap v m, LatCons m v)
    => Key m v -> Vert m

  -- | Will run all rules until there are no more to run.
  quiesce :: m ()

  -- | A rule:
  --
  --    - Has an initial vertex (type) to which it applies
  --    - Can read the lat member associated with a vertex
  --    - can see a single relation associated with the vertex (non-determinism
  --      is handled elsewhere)
  --    - Can add relations to the graph.
  --    - Can define whether lattice members are equal or subsume each other.
  --    - Should only every be upwards closed (i.e it can only increase the
  --      number of vertices or relations in the graph, and only push
  --      lattice values upwards.
  --    - Should die on pattern match failures and guard hitting fail. Other
  --      failures (i.e guards reading bottom) should just cause the transaction
  --      to abort and be reinserted as a hook.
  addRule :: (TermCons t m) => (Term t m -> m ()) -> m ()







-- | An edit captures a single concrete change we could make to our
--   lattice map.
--
--   When we use this within a free monad we have a
data Edit m a where

  AddTerm :: (MonadTermGraph m, TermCons t m)
    => t (Vert m) -> Edit m (Term t m)

  Put      :: (MonadLatMap v m, LatCons m v)
    => LatMemb m v -> Edit m (Key m v)

  Bind     :: (MonadLatMap v m, LatCons m v)
    => Key m v -> LatMemb m v -> Edit m (Key m v)

  Equals   :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m (Key m v)

  Subsumes :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m Bool
