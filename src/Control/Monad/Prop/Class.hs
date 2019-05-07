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

class (Monad m) => MonadProp m where

  -- | getKey and getVert define an isomorphism between vertices on the term
  --   graph and keys. getKey here should only fail when the type of v
  --   requested is incorrect.
  getKey :: forall v. (MonadTermGraph m, MonadLatMap v m, LatCons m v)
    => Vert m -> Maybe (Key m v)

  getVert :: forall v. (MonadTermGraph m, MonadLatMap v m, LatCons m v)
    => Key m v -> Vert m

  -- | Will run all rules until the
  quiesce :: m ()

  -- | A rule:
  --
  --    - Has an initial vertex to which it applies
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
  addRule :: (Vert m -> Transaction m ()) -> m ()

-- | An edit captures a single concrete change we could make to our
--   lattice map.
--
--   When we use this within a free monad we have a
data Edit m a where

  Put      :: (MonadLatMap v m, LatCons m v)
    => LatMemb m v -> Edit m (Key m v)

  Bind     :: (MonadLatMap v m, LatCons m v)
    => Key m v -> LatMemb m v -> Edit m (Key m v)

  Equals   :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m (Key m v)

  Subsumes :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m Bool

-- | A Transaction is a suspended computation over the map of terms. When
--   it suspends it could be:
--
--     - A set of hooks which can generate a bunch of transactions when a
--       key is modified.
--
--     - A set of concrete edits to the LatMap we can (presumably) analyse as
--       needed.
--
--     - A signal that this specific transaction is finished, and can be
--       discarded when we finish,
data Transaction m k where

  -- | This transaction will add hooks that trigger when specific lattice
  --   elements are updated.
  Watch :: HashMap k (k -> m (Transaction m k)) -> Transaction m k

  -- | This transaction represents a series of concrete operations that
  --   we can perform on a set of lattice elements, and the transaction that
  --   happens when we
  Run :: F (Edit m) ()  -> Transaction m k

instance (Eq k, Hashable k, Alternative m) => Semigroup (Transaction m k) where

  -- NOTE :: We use the Semigroup instance of `Alt` (in Data.Monoid) to allow the
  -- semigroup instance of HashMap to work over the transactions we return.
  -- With the appropriate choice of alternative instance (`Compose [] Lat`?)
  -- we should be able to extract a list of all the new transactions that were
  -- created.
  --
  -- The big problem here is with duplication of rules. If a rule creates
  -- another rule, should we delete the first?
  --
  -- In the case where create different rules based on what a particular
  -- variable resolves to. Well, it should be an upwards closed function that
  -- differentiates between cases so if one choice is taken the other shouldn't
  -- be.
  --
  -- I guess the case that's weird is if the created rules aren't a flat lattice,
  -- instead becoming something else yet. We might need to keep track of child
  -- rules as we run (each parent rule should have at most one child per object?)
  --
  (Watch m) <> (Watch m') = Watch . unAlt $ wrapAlt m <> wrapAlt m'
    where
      wrapAlt :: HashMap k (k -> m r) -> HashMap k (k -> Alt m r)
      wrapAlt = map (map Alt)

      unAlt :: HashMap k (k -> Alt m r) -> HashMap k (k -> m r)
      unAlt = map (map getAlt)

  -- When we have just have two free monads of edits we can concat them to get
  -- the resulting output.
  (Run f) <> (Run f') = Run $ f *> f'

  -- If we have a run and a watch, we watch on the relevant variables and
  -- append the potential side-effects together. Done this way, if we
  -- can create a sandbox for the edit operation, we can run an operation
  -- inside the sandbox and only commit them if certain conditions are met.
  -- (Hmm, flattened sandboxes == provenance == predicated operations. Just
  --  add an interpretation function that will turn a forall into a rule.)
  -- Making decisions with provenance seems like a bad idea.
  Run e   <> Watch m = Watch . map (\ fk k -> (Run e <>) <$> fk k) $ m
  Watch m <> Run e   = Watch . map (\ fk k -> (Run e <>) <$> fk k) $ m


instance (Eq k, Hashable k, Alternative m) => Monoid (Transaction m k) where
  mempty = Run $ pure ()
