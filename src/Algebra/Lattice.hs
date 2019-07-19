{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Algebra.Lattice where

import Ivy.Prelude


-- | A basic class for defining a partial order. Should be consistent with
--   the instance for @Eq@.
class (Eq l) => POrd l where

  lessThanOrEq    :: l -> l -> Bool
  lessThanOrEq a b = greaterThanOrEq b a

  lessThan        :: l -> l -> Bool
  lessThan a b = (lessThanOrEq a b) && (not $ a == b)

  greaterThanOrEq :: l -> l -> Bool
  greaterThanOrEq a b = lessThanOrEq b a

  greaterThan     :: l -> l -> Bool
  greaterThan a b = lessThan b a
  {-# MINIMAL lessThanOrEq | greaterThanOrEq #-}

-- | Lift POrd to constructors of kind @Type -> Type@.
--
--   We provide the ordering tests as a monadic action to allow
--   for explicit decomposition of these operations elsewhere.
class (Functor l) => POrd1 l where

  liftLessThanOrEq    :: (Monad m)
                      -- | Leq for the parameter type @p@.
                      => (p -> p -> m Bool)
                      -> l p -> l p -> m Bool
  liftLessThan        :: (Monad m)
                      => (p -> p -> m Bool)
                      -> l p -> l p -> m Bool
  liftGreaterThanOrEq :: (Monad m)
                    => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftGreaterThan     :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftEqualTo         :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftNotEqualTo      :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool


-- | Lattice elements of type @l@ that can produce errors of type @e@
--   in join operations.
--
--   NOTE :: It is possible to define define the lattice operations without
--          being able to define a partial order. (E.g. for monotonic
--          `(JoinSemiLattice e a, JoinSemiLattice e b) => a -> b`)
--          But it's very important, if there is a partial order, that the
--          lattice and the partial order are consistent.
class JoinSemiLattice e l where

  -- | Lattice join operation. Returning `Left e` means that the result
  --   of the join operation is Top, with an annotation of type @e@
  latJoin :: l -> l -> Either e l

-- | A meetsemilattice over some partial order l
class MeetSemiLattice l where

  -- | Lattice meet operation, returning a value of `Nothing` indicates
  --   that the result of the operation is bottom.
  latMeet :: l -> l -> Maybe l

-- | A complete lattice has both meet and join operations.
type Lattice e l = (JoinSemiLattice e l, MeetSemiLattice l)

class JoinSemiLattice1 e l where

  -- | Lift a join operation through a type constructor, such that
  --   all the expected lattice properties are met.
  --
  --   This is done in a monad context because decomposing join
  --   operations into parts is rather useful.
  --
  --   In addition, this interface will propagate errors that
  --   occur when joining subterms indiscriminately. There are
  --   cases where not propagating an error is the correct choice,
  --   but those will be looked at later.
  --
  --   NOTE :: We force you to use the join operation non-commutatively
  --          because we might need to handle each input differently.
  liftLatJoin   :: (Monad m)
                -- | The join operation we are lifting into 'l'
                => (a -> m c)
                -> (b -> m c)
                -> (a -> b -> m c)
                -> l a -> l b -> m (Either e (l c))


class MeetSemiLattice1 l where

  -- | Lift a meet operation through a type constructor, in
  --   such a way that allows us to decompose it explicitly.
  --
  --   We trust the user to check when an outcome is a
  --   representation of bottom and correctly return `Nothing`.
  liftLatMeet   :: (Monad m)
                -- | the meet operation we are lifting into `l`
                => (p -> p -> m (Maybe p))
                -> l p -> l p -> m (Maybe (l p))

type Lattice1 e l = (JoinSemiLattice1 e l, MeetSemiLattice1 l)
