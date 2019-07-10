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

-- | This is a term variable expression which stores some arbitrary depth
--   term in t, where all leaf nodes are `v`s. This is isomorphic to `UTerm t v`
--   from `unification-fd` but with shorter constructors.
--
--   TODO :: Consider just making this a set of pattern synonyms over `UTerm`.
data TV t v where

  -- | This is the constructor for a term, we keep it short because people
  --   will be using this rather a lot.
  T :: {getT :: !(t (TV t v))} -> TV t v

  -- | Constructor that holds a variable with some arbitrary phantom.
  --   This is mostly for convenience so that one doesn't need to cast
  --   values repeatedly.
  V :: {getV :: !v} -> TV t v

class (Traversable t, Eq1 t, Hashable1 t) => Unifiable t  where

  -- | I like the model where we just create constraints that cover
  --   various classes, and have one big'ol datatype to implement all
  --   of the potential errors.
  --
  --   Therefore, you get this constraint family to tell us what constraints
  --   an error should implement.
  type UnificationErr t e :: Constraint

  -- | Attempt to unify the following terms. A failure should return
  --   `Left e` and a success should return a `Right _` where
  --   any `Left (v,v)` will be further unified.
  --
  --   TODO :: Yeah, I know that latter type is getting to be a bit much
  --          but it'll do for now. It's not clear that a new datatype
  --          for this one use is actually useful.
  --
  --   TODO :: I should have a monad unify or something that just lets me
  --          define how unification occours and otherwise can just
  --          do it's thing.
  unifyTerm :: (UnificationErr t e)
            => t v -> t v
            -> Either e (t (Either (v,v) v))


-- | This class is a somewhat modified version of
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
--   Specifically, the rollback mechanism is meant to interact seamlessly
--   with query modes for modern SMT solvers. This mode allows you to
--   push and pop sets of constraints from a stack while preserving
--   any relevant learned clauses.
--
--   Note: We allow `m` to be of any kind because there's no real requirement it
--   be a monad or something. This interface explicitly chooses to not require
--   a way to extract m, since it could be a monad, a pure container, or
--   something else entirely.
--
--   Note: The operations `unify`, `equals`, `equiv`, and `subsume` /can/ all be
--   implemented in terms of the `*Var` operations, but in a number of
--   instances we will be able to get radical speedups by restricting `t`
--   and specializing those ops.
--
--   FIXME :: Having `Hook` as an associated type family in this class
--           renders the interface for hooks basically useless.
--           In a better world, we'd either:
--
--             1) Provide functions in this class that allow you to construct
--                a hook. (Good)
--
--             2) Standardize the structure of a hook so that it's just
--                a function of some sort. (Best)
class (Unifiable t, Semigroup (Hook m))
      => BindUpdate (m :: k) t | m -> t where

  -- | This is an update that tells us how to modify a unification map.
  --
  --   The intention is that an implementer doesn't export `res` to
  --   a user.
  type Update m = (res :: Type -> Type) | res -> m

  -- | This is a variable that has a unifiable term associated with it.
  --   generally defined by `m` in one way other.
  --
  --   The intention here is that `Var m` type is hidden from users
  --   such that they can only use the functions in this typeclass to
  --   work with them.
  type Var m :: Type

  -- | The type of hooks for this type of unification map.
  type Hook m :: Type

  -- | Create a new free (unbound) variable.
  freeVar :: Update m (Var m)

  -- | Get the single layer term for some variable or `Nothing` if
  --   the var is unbound.
  lookupVar  :: Var m -> Update m (Maybe (t (Var m)))

  -- | Binds a variable to some term, unifying it with any existing
  --   term for that variable if needed.
  bindVar :: Var m -> t (Var m) -> Update m ()

  -- | Unifies two variables and their associated terms. If the
  --   unification fails the transaction should be rolled back
  --   and some error returned through whatever error mechanism
  --   `Update m` uses.
  unify :: Var m -> Var m -> Update m (Var m)

  -- | Asserts that the first variable is <= the second.
  subsumes :: Var m -> Var m -> Update m Bool

  -- | Tells us whether two terms have been unified. Does not change
  --   the state of the update, just return information.
  equals :: Var m -> Var m -> Update m Bool

  -- | Tells us whether the input terms are equivalent modulo renaming of
  --   free variables. If they are, returns a set of unifications that
  --   need to occur for both terms to be truly equivalent.
  equiv :: Var m -> Var m -> Update m Bool

  -- | Adds a single hook to the unification map. Semantically this should
  --   use the semigroup instance of `Hook m` to merge the new hook with
  --   all previous hooks.
  --
  --   A hook, whatever the exact form it takes, should be triggered whenever
  --   there is a change to
  addHook :: Hook m -> Var m -> Update m ()

  -- | Returns the hook for some given variable.
  getHook :: Var m -> Update m (Hook m)

  -- | Given two updates, this produces a parallel merge of those two updates.
  --   really, it's the implementation of this that determines the degree of
  --   parallelism that's used as things update and actions are performed.
  --
  --   It's rather important that both updates use a split identifier space
  --   otherwise the final merge action can have aliasing errors.
  --
  --   If `Update m` is a monad then this can be taken from `MonadParallel`.
  merge    :: Update m a
           -> Update m b
           -> Update m (a,b)

  -- | Try an update, if the action should be rolled back (returns a `Left f`)
  --   then do so, and run the recovery function.
  --
  --   Keep in mind that the f here isn't actually an error per-se, just
  --   some knowledge that has been gained from the rolled back computation.
  --   Say if you're doing CDCL `f` would be the newly learned conflict clause.
  --
  --   An uncaught error in the initial action should rollback the state to
  --   the start of the action and then allow the error to continue propagating
  --   upward, without running the recovery action.
  --
  --   TODO :: Hmm, stacking additional monad transformer on top of this
  --          should be doable if they have @MonadTransControl@ instances.
  --          But hoo boy, I've got no idea how to do that in a way that
  --          preserves semantics.
  attempt :: Update m (Either f b) -> (f -> Update m b) -> Update m b

  -- | Combine one update which happens after another into a single
  --   (hopefully somehow compressed or minimized) update. This is probably
  --   just a bind of some sort if `Update m` is a monad.
  sequence :: Update m a -> (a -> Update m b) -> Update m b

-- TODO ::I intend to wrap this core interface to create an interface that
--       allows working with terms of many different types in parallel.
--       That way we can provide some solid foundation for layering
--       analysis over each other, having analysis that can interact
--       with monads above and below this on the stack.
--

-- Wait, this works badly with hooks since those triggering will themselves
-- fiddle with the system.
--
-- Well, it depends on the idempotence and general properties of unification.
-- If everything stays nice and upwards closed
data VarData h t v
  = Base { term :: t v, newSubs :: [v], newHooks :: [h], updated :: [v] }
  | Merged v

-- generator will probably be from concurrent-supply
-- ideally a vardata can be implicitly transformed into an m -> m
--
-- The hard part here is hooks, since those are dependent on what hooks
-- are given us with the m.
-- data Upd generator m = UPD (generator -> VarData h t v)
