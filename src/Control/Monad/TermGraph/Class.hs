{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : Control.Monad.TermGraph.Class
Description : Class for monads which can store a graph where edges are
              terms in grammar.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Control.Monad.TermGraph.Class where

import Ivy.Prelude

-- | This monad can handle graphs of relationships between Vertices of a graph
--   and terms in a language (semi-hyperedge things) that describe relationships
--   between vertices.
--
--   FIXME :: Do we need to have some operation to get the details of a
--           relationship?
class (Eq (Vert m), Hashable (Vert m), Monad m) => MonadTermGraph m where

  type Term (t :: * -> *) m :: *
  type Vert m :: *

  type TermCons (t :: * -> *) m :: Constraint

  -- | Given some relationship between vertices, adds it to the graph, and
  --   returns a reference to said relationship.
  addTerm :: (TermCons t m) => (t (Vert m)) -> m (Term t m)

  -- | Retrieves a "Single" term from the term graph. In general this will just
  --   take your operation on a term graph and
  getTerm :: forall t. (TermCons t m) => Term t m -> m (t (Vert m))

  -- | Given a particular vertex will retrieve terms (of one type) that
  --   involve said vertex. TODO :: Consider removing this, we shouldn't need it
  -- getTerms :: forall t. (TermCons t m) => Vert m -> m [t (Vert m)]
