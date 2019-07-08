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

module Ivy.Scratchpad where

import Ivy.Prelude
import Data.Functor.Contravariant
import Control.Monad.Trans.Control

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
--           term in our graph, rather than defining interfaces that
--           are to work over all terms?
--
--          It's a pretty important question since it determines how generic
--          our instances must be and how many different types of analysis
--          they ought to support.
--
--   NOTE :: Also we shouldn't worry too much about efficiency with rules since
--          that can be dealt with later. For now, just be slightly lazy in
--          in the application of rules, and probably treat definitions
--          as a separate class?
--
--   TODO :: Another major design decision to be made is about whether we
--          split up the union-find and definitional layers or have them
--          both handled by a single monolith.
--
--          - The former should be more reusable, since we're squishing the
--            term level semantics of a bunch of things down flat.
--
--          - The latter would likely be faster and easier to optimize.
--            I suspect it would be faster to build, but not as simple
--            to manipulate.
--
--

class MonadBind m => MonadUnify m  where

  -- | This allows you to unify terms in your given context.
  unify :: (Unifiable e t, MonadError e m) => t (Var m t) -> t (Var m t) -> m (Var m t)

  -- | Tells us whether two terms have been unified. Does not change
  --   the state of the update, just return information.
  equals :: (Unifiable e t, MonadError e m) => t (Var m t) -> t (Var m t) -> m Bool

-- | Lets you define how unification works for some specific type of term.
class Unifiable e t where

   -- | TODO :: see if we can better integrate with the partial order model
   --           that we're using elsewhere.
   unifyTerm :: (MonadError e m, MonadUnify m) => t v -> t v -> m (t v)

-- | Monads that allow you to bind variables to terms.
class MonadBind m where

  -- | This is a variable that has a unifiable term associated with it.
  type Var m :: (Type -> Type) -> Type

  -- | Create a new free (unbound) variable. The proxy term is a bit annoying
  --   but at least it helps ensure that everything is properly typed without
  --   requiring a whole pile of extra effort.
  freeVar :: (MonadError e m, Unifiable e t) => TypeRep t -> m (Var m t)

  -- | Get the single layer term for some variable or `Nothing` if
  --   the var is unbound.
  lookupVar  :: (MonadError e m, Unifiable e t) => Var m t -> m (Maybe (t (Var m t)))

  -- | Binds a variable to some term, unifying it with any existing
  --   term for that variable if needed.
  bindVar :: (MonadError e m, Unifiable e t) => Var m t -> t (Var m t) -> m (Var m t)


class (MonadBind m, MonadUnify m) => MonadSubsume m where

  -- | Asserts that the first variable is <= the second.
  subsumes :: Var m t -> Var m t -> m Bool

  -- | Tells us whether the input terms are equivalent modulo renaming of
  --   free variables. If they are, returns a set of unifications that
  --   need to occur for both terms to be truly equivalent.
  equiv :: Var m t -> Var m t -> m (Maybe [(Var m t, Var m t)])

-- | This captures injective relationships between terms. Which is to
--   say that a vertex may be the target of many relations, but each source
--   can only have one relation of a given type.
--
--   FIXME :: This interface should be a bit more concrete.
class (MonadBind m) => MonadRelate m where

  -- | Declare that the first variable is related to the second
  --   variable.
  --
  --   NOTE :: if you unify the source of a relation, with another source,
  --           their corresponding relations will also unify.
  newRelation :: (Unifiable e t, Unifiable e t', MonadError e m)
              => Var m t -> Var m t' -> m ()

  -- | Get the target of a relation (of some type t') when given a source.
  getTarget :: (Unifiable e t, Unifiable e t', MonadError e m)
            => TypeRep t' -> Var m t -> m (Var m t')


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
