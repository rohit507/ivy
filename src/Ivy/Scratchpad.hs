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

import Data.Coerce

class (Monad m) => MonadLat m where

  type IsLatErr m :: * -> Constraint

  top :: (IsLatErr m e) => e -> m a
  default top :: (MonadError e m, IsLatErr m e) => e -> m a
  top = throwError

  val :: a -> m a
  default val :: (Monad m) => a -> m a
  val = pure

  bot :: m a
  default bot :: (MonadPlus m) => m a
  bot = empty


class POrd l where

  lessThanOrEq :: (MonadLat m) => l -> l -> m Bool

  lessThan :: (MonadLat m) => l -> l -> m Bool

  greaterThanOrEq :: (MonadLat m) => l -> l -> m Bool

  greaterThan :: (MonadLat m) => l -> l -> m Bool

  equalTo :: (MonadLat m) => l -> l -> m Bool

  notEqualTo :: (MonadLat m) => l -> l -> m Bool

class LatticeMember l where

  latBottom :: l

  latJoin :: (MonadLat m) => l -> l -> m l

  latMeet :: (MonadLat m) => l -> l -> m l

class POrd1 l where

  liftLessThanOrEq :: (MonadLat m, POrd p) => l p -> l p -> m Bool

  liftLessThan :: (MonadLat m, POrd p) => l p -> l p -> m Bool

  liftGreaterThanOrEq :: (MonadLat m, POrd p) => l p -> l p -> m Bool

  liftGreaterThan :: (MonadLat m, POrd p) => l p -> l p -> m Bool

  liftEqualTo :: (MonadLat m, POrd p) => l p -> l p -> m Bool

  liftNotEqualTo :: (MonadLat m, POrd p) => l p -> l p -> m Bool

class LatticeMember1 l where

  liftLatBottom :: (LatticeMember p) => l p

  liftLatJoin :: (MonadLat m, LatticeMember p) => l p -> l p -> m (l p)

  liftLatMeet :: (MonadLat m, LatticeMember p) => l p -> l p -> m (l p)

infixr 0 :-^

data a :-^ b where

  UCFInt ::(LatticeMember a, LatticeMember b) =>
    (forall m. (MonadLat m) => a -> m b) -> a :-^ b

  UCFId :: (a :~: b) -> a :-^ b

instance Category (:-^) where

  id = UCFId Refl

  (UCFId  r) . (UCFInt a) = UCFInt $ fmap (castWith r) . a
  (UCFInt a) . (UCFId  r) = UCFInt $ a . castWith r
  (UCFInt a) . (UCFInt b) = UCFInt (b >=> a)



{-


  id = UCF id
  (UCF f) . (UCF g) = UCF $ f . g

data Lat a where
  Val :: a -> Lat a
  Bot :: Lat a

data LTerm l k where
  T :: Base l (LTerm l k) -> LTerm l k
  V :: k -> LTerm l k



class (Eq l) => PartiallyOrdered l where

  isBot :: l -> Bool

  -- Okay, so these will just pattern match

  lessThanOrEq   :: l -> l -> Lat Bool
  lessThanOrEq = undefined

  lessThan :: l -> l -> Lat Bool
  lessThan = undefined

  greaterThanOrEq :: l -> l -> Lat Bool
  greaterThanOrEq = undefined

  greaterThan :: l -> l -> Lat Bool
  greaterThan = undefined

  equalTo :: l -> l -> Lat Bool
  equalTo = undefined

  notEqualTo :: l -> l -> Lat Bool
  notEqualTo = undefined

class (PartiallyOrdered l) => Lattice l where

  joinLT  :: (Monad m) => (l -> l -> m (Lat l)) -> l -> l -> m (Lat l)
  joinLT = undefined -- TODO :: Assemble a full term if possible, use Data.Reify
                     --        to decompose result into its constituent parts

  meetLT :: (Monad m) => (l -> l -> m (Lat l)) -> l -> l -> m (Lat l)
  meetLT = undefined -- TODO :: Same as joinLT

  -- -- Given that the implementer of the following needs to make things work
  -- -- for every monad they don't really have leeway to do anything that they
  -- -- couldn't in a pure function, except to give us a hook

  -- leqL :: (Monad m) => (l -> l -> m Bool) -> l -> l -> m Bool
  -- leqL = undefined -- The idea is that

  -- joinL :: (Monad m) => (l -> l -> m l) -> l -> l -> m (Lat l)
  -- joinL = undefined

  -- meetL :: (Monad m) => (l -> l -> m l) -> l -> l -> m (Lat l)
  -- meetL = undefined

  -- {-# MINIMAL isBot , (leqLT, joinLT, meetLT) | (leqL , joinL , meetL) #-}

class (Monad m) => MonadLatticeMap m where

  type LatMapErr m :: Constraint
  data Key m l :: *

  newLat :: (Lattice l) => l -> m (Key m l)

  bindLat :: (Lattice l) => Key m l -> l -> m (Key m l)

  getLat :: (Lattice l) => Key m l -> m l

  equals :: (Lattice l) => Key m l -> Key m l -> m (Key m l)

  subsumes :: (Lattice l) => Key m l -> Key m l -> m Bool

class (MonadLatticeMap m) => MonadLatticeProp m where

  run :: Key m a -> (forall n. MonadLatticeMap n => a -> n ()) -> m ()

  watch :: Key m a -> [a -> m ()] -> m ()


uAnd :: MonadLatticeProp m => Lat Bool -> Lat Bool -> Lat Bool
uAnd a b = fall a <|> fall b <|> base

  where

    fall :: m Bool -> m Bool
    fall = undefined

    base :: m Bool
    base = (&&) <$> a <$> b

uOr :: MonadLatticeProp m => Lat Bool -> Lat Bool -> Lat Bool
uOr a b = fall a <|> fall b <|> base

  where

    fall :: m Bool -> m Bool
    fall b = undefined

    base :: m Bool
    base = (||) <$> a <$> b
-}
