
{---# LANGUAGE AllowAmbiguousTypes #-}
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


-- | This monad gives you the ability to unify terms in some unifiable language.
class MonadBind t m => MonadUnify t m  where

  -- | This allows you to unify terms in your given context.
  unify :: (Unifiable e t, MonadError e m) => t (Var m t) -> t (Var m t) -> m (Var m t)

  -- | Tells us whether two terms have been unified. Does not change
  --   the state of the update, just return information.
  equals :: (Unifiable e t, MonadError e m) => t (Var m t) -> t (Var m t) -> m Bool

-- | A property is a many-to-one relationship between two terms of potentially
--   different types.
class Property p t t' | p -> t, p -> t'

-- | A binding monad that can support property relations between terms.
--
--   NOTE: A very important note is that when you unify two terms with the same
--         property then the terms those properties point to will also be
--         unified!
class MonadProperty p m where

  -- | Retrieve the term re
  propertyOf :: (Property p t t', MonadBind t m, MonadBind t' m)
             => p -> Var m t -> m (Var m t')


-- | Lets you define how unification works for some specific type of term.
--
--   Ideally this would either be some JoinSemiLattice or the fixed point of a
--   higher-order join semilattice.
--   Those instances will be coming I suppose.
class Unifiable e t where

   -- | TODO :: see if we can better integrate with the partial order model
   --           that we're using elsewhere.
   unifyTerm :: (MonadError e m, MonadUnify t m) => t v -> t v -> m (t v)

-- | Monads that allow you to bind variables to terms.
class MonadBind t m where

  -- | This is a variable that has a unifiable term associated with it.
  type Var t m = r | r -> t m

  -- | Create a new free (unbound) variable. The proxy term is a bit annoying
  --   but at least it helps ensure that everything is properly typed without
  --   requiring a whole pile of extra effort.
  freeVar :: (MonadError e m, Unifiable e t) => TypeRep t -> m (Var t m)

  -- | Get the single layer term for some variable or `Nothing` if
  --   the var is unbound.
  lookupVar  :: (MonadError e m, Unifiable e t) => Var t m -> m (Maybe (t (Var t m)))

  -- | Binds a variable to some term, unifying it with any existing
  --   term for that variable if needed.
  bindVar :: (MonadError e m, Unifiable e t) => Var t m -> t (Var t m) -> m (Var t m)

class (MonadBind t m, MonadUnify t m) => MonadSubsume t m where

  -- | Asserts that the first variable is <= the second.
  subsumes :: Var m t -> Var m t -> m Bool

  -- | Tells us whether the input terms are equivalent modulo renaming of
  --   free variables. If they are, returns a set of unifications that
  --   need to occur for both terms to be truly equivalent.
  equiv :: Var m t -> Var m t -> m (Maybe [(Var m t, Var m t)])


-- | A class for monads that can attempt a computation and if that computation
--  fails rewind state and run some recovery operation
class MonadAttempt m where

  -- | Try an update, if the action should be rolled back (returns a `Left f`)
  --   then do so, and run the recovery function.
  --
  --   Keep in mind that the f here isn't actually an error per-se, just
  --   some knowledge that has been gained from the rolled back computation.
  --   E.g. if you're doing CDCL `f` could be a newly learned conflict clause.
  attempt :: m (Either f b) -> (f -> m b) -> m b



-- So what we want:
--
--    Term Graph w/ vertices in a language and relations to terms in multiple
--    related languages.
--
--    newVar :: m (Vert t m)
--
--    The ability to attempt a computation and then rewind state if/when there's
--    an issue.
--
--    Define unification rules for each type of term in the language
--    Define hooks that trigger when the definition of a term is updated
