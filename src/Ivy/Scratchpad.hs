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


class (Traversable t, Eq1 t, Hashable1 t)
      => Unifiable t  where

  type UnificationErr t e :: Constraint

  unifyTerm :: (UnificationErr t e) => t v -> t v -> Either e (t (Either (v,v) v))


-- | This class presents a map of variables to (recursive) terms in a
--   continuation passing style.
--
--   Yeah, CPS style is unusual and a bit more complicated than it
--   probably needs to be, but it allows for much finer control of
--   what actions happen when, and what they do.
--
--   Really, the fundamental goal of this interface is to allow backtracking
--   over sets of changes, while preserving useful information from them and
--   preventing leaks of references from domain to domain.
--
--   We allow `m` to be of any kind because there's no real requirement it
--   be a monad or something. This interface explicitly chooses to not require
--   a way to extract m, since it could either be a monad of some sort or
--   just a classic container.
class (Unifiable t) => UnificationMap (m :: k) t | m -> t where

  -- | This is an update that tells us how to modify a unification map.
  type Update m = (res :: Type -> Type) | res -> m

  -- | This is a variable that has a unifiable term associated with it.
  --   generally defined by `m` in one way other.
  type Var m :: Type

  -- | If we want to manage hooks in some way, we can give them keys so
  --   we can recover or manipulate them.
  type HookKey m :: Type

  -- | The type of hooks for this type of unification map.
  type Hook m :: Type

  -- | Pass in a continuation that uses a new variable to get a map update
  --   and get the corresponding update.
  --
  --   We use a first order type here in order to limit the scope of
  --   variable being created. As it is, one shouldn't be able to
  --   extract a key from the continuation
  freeVar :: Update m (Var m)

  -- | Sets a variable to some term, in this case we use the
  --   convenient little existential type wrapper for vars to
  --   make them mildly easier to work with.
  --
  --   This should probably be set up so that the only way to
  --   extract one of these vars is in a new context that
  setVar :: t (Var m) -> Var m -> Update m ()

  -- | Asserts that the first variable is <= the second.
  subsumes :: (Var m) -> (Var m) -> Update m Bool

  -- | Tells us whether two terms have been unified. Does not change
  --   the state of the update, just return information.
  equals :: (Var m) -> (Var m) -> Update m Bool

  -- | Get the single layer term for some variable or `Nothing` if
  --   the var is unbound.
  getTerm  :: Var m  -> Update m (Maybe (t (Var m)))

  -- | Given two updates, this produces a parallel merge of those two updates.
  --   really, it's the implementation of this that determines the degree of
  --   parallelism that's used as things update and actions are performed.
  --
  --   It's rather important that both updates use a split identifier space
  --   otherwise the final merge action can have aliasing errors.
  merge    :: Update m a
           -> Update m b
           -> Update m (a,b)

  -- | Adds a single hook to the unification map, by default
  addHook :: HookKey m -> Hook m -> Var m -> Update m ()
  addHook k h v = addHooks [(k,[h])] v

  -- | Add hooks that are run when the term for some variable is changed.
  --   Yeah, this is a bit weird, since it's how we basically create
  --   propagator update hooks.
  addHooks :: [(HookKey m, [Hook m])]
          -> Var m
          -> Update m ()

  -- | Retrieves all the hooks for some given key and var.
  getHooks :: HookKey m -> Var m -> Update m [Hook m]

  -- | Gets every hook for some given key.

  -- | Removes all the hooks for a variable under some key.
  removeHooks :: HookKey m -> Var m -> Update m [Hook m]

  -- | Try an update, if the action should be rolled back (returns a `Left f`)
  --   then do so, and run the recovery function.
  --
  --   Keep in mind that the f here isn't actually an error per-se, just
  --   some knowledge that has been gained from the rolled back computation.
  --   Say if you're doing CDCL `f` would be the newly learned conflict clause.
  --
  --   The semantics if you do hit an error within the initial transaction
  --   aren't super well defined
  attempt :: Update m (Either f s) -> (f -> Update m b) -> Update m (Either b s)

  -- | Combine one update which happens after another into a single
  --   (hopefully somehow compressed or minimized) update. This is probably
  --   just a bind of some sort.
  sequence :: Update m a -> (a -> Update m b) -> Update m b


{-
-- | If you have an expression, generate a new variable
newVar :: (Monad (Update m v t), UnificationMap e m t) => TV t v -> Update m v t v
newVar = __TODO

unify :: forall e m t v. (UnificationMap e m t, Ref v, Monad (Update m v t), Semigroup e)
      => v -> v -> Update m v t (Either e v)
unify a b = do
  eta <- getTerm @e @m a
  etb <- getTerm @e @m b
  case (eta,etb) of
    (Left e, Left e') -> pure . Left $ e <> e'
    (Left e, _) -> pure . Left $ e
    (_, Left e) -> pure . Left $ e
    (ta, tb) -> __TODO
    -- Try unifying the term, w/in a wrapper that assumes a and b are merged.
    -- if you get an error out then return that.
    -- otherwise, traverse through the term replacing pairs and terms
    -- with `Either e a`
    --   if there are 1 or more errors, `<>` them and return that
    --   if not then bind the result term to a and return a
-}
