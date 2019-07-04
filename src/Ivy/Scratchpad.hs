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

module Ivy.Scratchpad where

import Ivy.Prelude

class Generator v g | g -> v where
  get   :: g -> (v , g)
  split :: g -> (g , g)

type Ref v = (Eq v, Hashable v)

data TV t v = T (t (TV t v)) | V v

class (Semigroup e, Traversable t, Eq1 t, Hashable1 t)
                => Unifiable e (t :: Type -> Type) where
  unifyTerm :: (Ref v, UnificationMap e m t)
            => t v -> t v -> Either e (t (Either (v,v) v))

-- | This class presents a map of variables to (recursive) terms in a
--   continuation passing style.
class (Unifiable e t)
        => UnificationMap e (m :: Type) (t :: Type -> Type) | m -> t where

  -- | This is an update that tells us how to modify a unification map.
  type Update m v t :: Type -> Type

  type Frozen m v t :: Type -> Type

  -- | Pass in a continuation that uses a new variable to get a map update
  --   and get the corresponding update.
  freeVar  :: (Ref v) => Update m v t v

  -- | Binds a term to a variable
  bindVar  :: (Ref v) => v -> TV t v -> Update m v t ()

  -- | The first variable is <= the second
  subsumes :: (Ref v) => v -> v -> Update m v t (Maybe e)

  -- | Given two updates, this produces a parallel merge of those two updates.
  --   really, it's the implementation of this that determines the degree of
  --   parallelism that's used as things update and actions are performed.
  merge    :: (Ref v) => Update m v t a -> Update m v t b -> Update m v t (a,b)

  -- | If you give it a variable whose term you want to get, and what you
  --   intend to do with that term, then this returns the final update
  getTerm  :: (Ref v) => v -> Update m v t (Either e (t v))

  -- | Given a generator and an update action, this will generate the
  --   concrete final mapping that contains all the (fully cyclical)
  --   post unification terms.
  build :: (Ref v, Generator v g) => g -> Update m v t b -> Either e (b, m)

  -- | Modify an error, usually used to add context to a low level error.
  modifyError :: (e -> e) -> Update m v t a -> Update m v t a


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
