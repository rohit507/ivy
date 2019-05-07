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
class (Monad m) => MonadTermGraph m where

  type Rel m :: *
  type Vert m :: *

  type RelCons (r :: * -> *) m :: Constraint

  -- | Given some relationship between vertices, adds it to the graph, and
  --   returns a reference to said relationship.
  addTerm :: (RelCons r m) => (r (Vert m)) -> m (Rel m)

  -- | Given a particular vertex will retrieve a relationship that
  --   involve said vertex. FIXME :: figure out whether we want to handle
  --   non-determo
  getTerms :: Vert m -> m [Rel m]
