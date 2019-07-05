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

class Generator v g | g -> v where
  get   :: g -> (v , g)
  split :: g -> (g , g)


-- | This is a term variable expression which stores some arbitrary depth
--   term in t, where all leaf nodes are Vars.
--
--   This object should only ever be provided by the user, and never
--   given to them, since it destroys all the scoping information for
--   vars inside it.
--
--   Yeah, that means it can be used to sneak vars out of the scope in which
--   they were established, I'll see if there's a way to prevent that
--   in what we're up to.
--
--   I'm not actually sure there is a way to do that. :|
--
--   TODO :: Switch this back to the `TV t v` model where it's isomorphic to a
--          UTerm.
data TV (m :: Type -> Type) where

  -- | This is the constructor for a term, we keep it short because people
  --   will be using this rather a lot.
  T :: (UnificationMap e m t) => {getT :: t (TV m)} -> TV m

  -- | Constructor that holds a variable with some arbitrary phantom.
  --   This is mostly for convenience so that one doesn't need to cast
  --   values repeatedly.
  V :: (UnificationMap e m t) => Var m v -> TV m

-- | This is an existentially quantified variable we use to ease the
--   burden of constructing a new term.
data EV (m :: Type -> Type) where
  EV :: (UnificationMap e m t) => Var m v -> EV m

class (Semigroup e, Traversable t, Eq1 t, Hashable1 t)
      => Unifiable e (t :: Type -> Type) where

  unifyTerm :: t v -> t v -> Either e (t (Either (v,v) v))

-- | This allows hooks to manage their own cleanup operations, ideally
--   in a way that will effectively get rid of unneccesary ones.
data HookStatus m where
  Keep :: HookStatus m
  Discard :: HookStatus m
  Replace :: UnificationMap e m t
          => (forall v. t (Var m v) -> t (Var m v) -> Update m (HookStatus m))
          -> HookStatus m

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
--   TODO :: Remove CPS style from this class and just let the instances
--          definition of `Update m` do its thing.
--
--   TODO :: Consider just not trying to manage the scope of variables with all
--          the foralls.
class (Unifiable e t)
        => UnificationMap e (m :: Type -> Type) (t :: Type -> Type) | m -> t, t -> e where

  -- | This is an update that tells us how to modify a unification map.
  type Update m = (res :: Type -> Type) | res -> m

  -- | The variables, or references to them, which are bound to terms
  --   in the resulting map.
  --
  --   Ideally the `v` in any `Var m v` is a phantom type variable.
  --   Which only exists to ensure that we don't leak variables out of scope.
  --
  --   Ideally any instances of this class would hide the actual type and
  --   constructor used for `Var m`.
  type Var m = (res :: Type -> Type) | res -> m

  -- | Pass in a continuation that uses a new variable to get a map update
  --   and get the corresponding update.
  --
  --   We use a first order type here in order to limit the scope of
  --   variable being created. As it is, one shouldn't be able to
  --   extract a key from the continuation
  freeVar :: (forall v. Var m v -> Update m a) -> Update m a

  -- | Sets a variable to some term, in this case we use the
  --   convenient little existential type wrapper for vars to
  --   make them mildly easier to work with.
  --
  --   This should probably be set up so that the only way to
  --   extract one of these vars is in a new context that
  setVar  :: Var m v -> t (EV m) -> Update m a -> Update m a

  -- | The first variable is <= the second.
  subsumes :: Var m v -> Var m v' -> (Bool -> Update m a) -> Update m a

  -- | Tells us whether two terms have been unified.
  equals :: Var m v -> Var m v' -> (Bool -> Update m a) -> Update m a

  -- | Given two updates, this produces a parallel merge of those two updates.
  --   really, it's the implementation of this that determines the degree of
  --   parallelism that's used as things update and actions are performed.
  merge    :: Update m a
           -> Update m b
           -> Update m (a,b)

  -- | Add a hook that is run when the term for some variable is changed.
  --   Yeah, this is a bit weird, since it's how we basically create
  --   propagator update hooks.
  --
  --   Keep in mind this is
  addHook :: Var m v
          -> (forall v'. t (Var m v') -> t (Var m v') -> Update m (HookStatus m))
          -> Update m ()

  -- | Try an update, if the action should be rolled back (returns a `Left f`)
  --   then do so, and run the recovery function.
  --
  --   Keep in mind that the f here isn't actually an error per-se, just
  --   some knowledge that has been gained from the rolled back
  attempt :: Update m (Either f s) -> (f -> Update m b) -> Update m (Either b s)

  -- | Combine one update which happens after another into a single
  --   (hopefully somehow compressed or minimized) update. This is probably
  --   just a bind of some sort.
  sequence :: Update m a
           -> (a -> Update m b)
           -> Update m b

  -- | If you give it a variable whose term you want to get, and what you
  --   intend to do with that term, then this returns the action after that
  --   point.
  getTerm  :: Var m v
           -> (forall v'. Either e (t (Var m v')) -> Update m a)
           -> Update m a


foo :: (UnificationMap e m t) =>  Update m ()
foo = freeVar (\ a -> freeVar (\ b -> subsumes a b undefined))

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
