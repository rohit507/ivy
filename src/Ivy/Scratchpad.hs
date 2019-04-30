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

infixr 0 :-^

data a :-^ b where
  UCF :: (a -> Lat b)

instance Category (:-^) where
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
