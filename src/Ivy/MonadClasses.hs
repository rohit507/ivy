{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
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

import Intro hiding (Item)
import Ivy.Prelude
import Algebra.Lattice

-- import qualified Data.Text as Text
-- import Data.HashSet (HashSet)
-- import qualified Data.HashSet as HS
-- import Ivy.Assertions

-- import Data.Monoid (All, getAll)

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


-- | A context that is an instance of MonadBind can create variables that
--   represent single terms in a recursive expression, as well as rebind them
--   to new values, and declare that one variable should be redirected into
--   another.
class ( Typeable t
      , Typeable m
      , Traversable t
      , JoinSemiLattice1 e t
      , Eq1 t
      , Monad m
      , Show (Var m t)
      , Hashable (Var m t)
      , Ord (Var m t)
      , MonadError e m)
    => MonadBind (e :: Type) m t | m -> e where

  type Var m :: (Type -> Type) -> Type

  -- | Create a free variable with no term bound to it
  freeVar :: m (Var m t)

  -- | lookup the term for a variable, returns Nothing if the variable is free.
  --   the first parameter is a TH generated hash. Users should use `$lookupVar`
  lookupVar' :: Int -> Var m t -> m (Maybe (t (Var m t)))

  -- | Binds the given term to a variable.
  bindVar   :: Var m t -> t (Var m t) -> m (Var m t)

  -- | Deletes the contents of the first variable, and makes all references to
  --   it instead point to second variable.
  redirectVar :: Var m t -> Var m t -> m (Var m t)

  -- | Does not modify the state of m at all, but returns the most up to date
  --   variable that is equivalent to the input.
  --
  --   Forall a b in Var m t
  --      unified a b === (==) <$> freshenVar a <*> freshenVar b
  --
  --   after two calls to freshen var, two terms should be unified only if they're
  freshenVar :: Var m t -> m (Var m t)

newVar :: (MonadBind e m t) => t (Var m t) -> m (Var m t)
newVar t = do
  v <- freeVar
  bindVar v t

eqVar :: (MonadBind e m t) => Var m t -> Var m t -> m Bool
eqVar a b = (==) <$> freshenVar a <*> freshenVar b

-- | effective type is `MonadBind e m t => Var m t -> m (Maybe (t (Var m t))`
lookupVar :: Q Exp
lookupVar = [|lookupVar' (hash $(liftLoc =<< location))|]

-- | Properties are singleton types which reference some functional relation
--   between terms.
class (Typeable p, Typeable (From p), Typeable (To p)) => Property p where
  type From p :: Type -> Type
  type To   p :: Type -> Type

  rep :: p

class (Monad m, MonadBind e m (From p), MonadBind e m (To p), Property p) => MonadProperty e p m where

  -- | This will get the property related to the input term, generating a
  --   free term if it does not already exist.
  --
  --   Properties are many-to-one relationships between terms. For instance
  --   many terms can have the same type, but no term can have multiple
  --   types.
  propertyOf :: p -> Var m (From p) -> m (Var m (To p))

-- | This class is only relevant to implementers of a MonadProperty.
--   Basically, it gives us a way to traverse each of the potential
--   property pairs for some term, and appropriately handle them.
class MonadProperties e m where

  getPropertyPairs :: forall a t. (MonadBind e m t)
      => (forall proxy p. (From p ~ t
                         , MonadAssume e m (To p)
                         , MonadProperty e p m
                         , Property p)
                      => proxy p -> These (Var m (To p)) (Var m (To p)) -> m a)
      -> (a -> a -> m a)
      -> a
      -> Var m t -> Var m t -> m a

-- | This class is mostly only relevant to implementers of a MonadBind.
--   In effect we refactor the visited sets as assumptions that are held
--   during some part of the computation.
--
--   This basically makes it easier to handle coinductive reasoning about
--   equality, unity, and subsumption.
class (MonadBind e m t) => MonadAssume e m t where


  -- | Within the passed action assume the two variables are equivalent.
  assumeEqual :: Var m t -> Var m t -> m a -> m a

  -- | Within the passed action assume the two variables are unified.
  assumeUnified :: Var m t -> Var m t -> m a -> m a

  -- | Within the passed action assume that the first variable subsumes the
  --   second. .
  assumeSubsumed :: Var m t -> Var m t -> m a -> m a

  -- | set global state
  assertEqual :: Var m t -> Var m t -> m ()
  assertUnified :: Var m t -> Var m t -> m ()
  assertSubsumed :: Var m t -> Var m t -> m ()

  isAssumedEqual :: Var m t -> Var m t -> m Bool
  isAssumedUnified :: Var m t -> Var m t -> m Bool
  isAssumedSubsumed :: Var m t -> Var m t -> m Bool

-- | Rules allow for the enforcement of relationships between terms as an
--   operation is performed.
class ( forall g. (MonadBind     e m g) => MonadBind e (Rule m) g
      , forall k. (MonadAssume   e m k) => MonadAssume e (Rule m) k
      , forall p. (MonadProperty e p m) => MonadProperty e p (Rule m)
      , MonadError e m
      , GetErr (m)
      , GetErr (Rule m)
      , e ~ Err m
      , Err m ~ Err (Rule m)
      , MonadRule e (Rule m)
      , Rule (Rule m) ~ (Rule m)
      , Var m ~ Var (Rule m)
      ) => MonadRule e m | m -> e where

  type Rule m :: Type -> Type

  -- | Default implementation exists for r ~ m, where addRule is just identity.
  --   since any recursively defined rules should just become a single
  --   larger rule.
  addRule :: Rule m () -> m ()
  default addRule :: (Rule m ~ m) => Rule m () -> m ()
  addRule = id
