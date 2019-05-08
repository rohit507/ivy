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
class (Monad m) => MonadTermGraph m where

  type Term m :: *
  type Vert m :: *

  type TermCons (t :: * -> *) m :: Constraint

  -- | Given some relationship between vertices, adds it to the graph, and
  --   returns a reference to said relationship.
  addTerm :: (TermCons t m) => (t (Vert m)) -> m (Term m)

  -- | Given a particular vertex will retrieve relationships that
  --   involve said vertex.
  --
  --   FIXME :: Consider having the default version pre-filter the Rels somehow?
  getTerms :: Vert m -> m [Term m]
