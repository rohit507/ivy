{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.MonadClasses where

import Ivy.Prelude
import Algebra.Lattice
import qualified Data.Text as Text

-- * These classes are components of a somewhat modified version of
--   `Control.Unification.BindingMonad` from `unification-fd`. It
--   still performs structural unification, but with a few key differences:
--
--     1) It doesn't choke on cyclic terms.
--     2) Provides a rollback mechanism that can still return information
--        from reverted branches of execution.
--     3) Triggers hooks when terms are unified.
--
--   All of these properties are desired if we want to use unification
--   as a significant part of a synthesis process, or as an element in the
--   analysis of inherently cyclic term graphs.
--
--   TODO :: Should we go back to being more explicit about the type of each
--           term in our graph, rather than definingn to be made is about whether we
--          split up the union-find and definitional layers or have them
--          both handled by a single monolith.
--
--          - The former should be more reusable, since we're squishing the
--            term level semantics of a bunch of things down flat.
--
--          - The latter would likely be faster and easier to optimize.
--            I suspect it would be faster to build, but not as simple
--            to manipulate.

type Term   e t = (JoinSemiLattice1 e t, Traversable t)
type Binder e m = (MonadError e m, BindingError e)

class MonadBind t m where

  type Var m = (res :: (Type -> Type) -> Type) | res -> m

  freeVar   :: m (Var m t)

  lookupVar :: Var m t -> m (Maybe (t (Var m t)))

  bindVar   :: Var m t -> t (Var m t) -> m (Var m t)

class Property p t t' | p -> t, p -> t'

class MonadProperty p m where

  propertyOf :: (MonadBind t m, MonadBind t' m, Property p t t')
      => p -> Var m t -> m (Var m t')

  getOverlappingProperties :: (Monoid a, MonadBind t m)
      => (forall t'. (Property p t t', MonadBind t' m) => Var m t' -> Var m t' -> m a)
      -> Var m t -> Var m t -> m a

class (MonadBind t m) => MonadAssume t m where

  isEqualTo :: Var m t -> Var m t -> m Bool

  assumeEqual :: Var m t -> Var m t -> m a -> m a

  isUnifiedWith :: Var m t -> Var m t -> m Bool

  assumeUnified :: Var m t -> Var m t -> m a -> m a

  isSubsumedBy :: Var m t -> Var m t -> m Bool

  assumeSubsumed :: Var m t -> Var m t -> m a -> m a

class ( forall t. (MonadBind t m) => MonadBind t (r m)
      , forall p. (MonadProperty p m) => MonadProperty p (r m)
      ) => MonadRule r m where

  addGeneralRule :: (MonadBind t m) => (Var m t -> r m ()) -> m ()

  addSpecificRule :: r m () -> m ()

class BindingError e
