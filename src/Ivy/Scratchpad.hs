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

infixr 0 (:-^)

data a :-^ b where
  UCF :: (a -> b)

instance Category (:-^) where
  id = UCF id
  (UCF f) . (UCF g) = UCF $ f . g

data Lat a where
  Top :: Dynamic -> Lat a
  Val :: a -> Lat a
  Bot :: Lat a

data LTerm l k where
  T :: Base l (LTerm l k) -> LTerm l k
  V :: k -> LTerm l k

class LatticeMember l where

  isBot :: l -> Bool

  leqLT   :: LTerm l k -> LTerm l k -> Lat Bool
  leqLT = undefined

  joinLT  :: LTerm l k -> LTerm l k -> Lat (LTerm l (Either k (k,k))
  joinLT = undefined

  meetLT :: LTerm l k -> LTerm l k -> Lat (LTerm l (Either k (k,k))
  meetLT = undefined

  leqL :: l -> l -> Lat Bool
  leqL = undefined

  joinL :: l -> l -> Lat l
  joinL = undefined

  meetL :: l -> l -> Lat l
  meetL = undefined

  {-# MINIMAL isBot , (leqLT, joinLT, meetLT) | (leqL , joinL , meetL) #-}

class (Monad m, MonadError e m, LatMapErr e) => MonadLatticeMap m where

  type LatMapErr :: * -> Constraint
  data Key m l :: *

  newLat :: (LatticeMember l)
         => LTerm l (Key m l) -> m (Key m l)

  bindLat :: (LatticeMember l)
          => Key m l -> LTerm l (Key m l) -> m (Key m l)

  getLat :: (LatticeMember l)
         => Key m l -> m (LTerm l (Key ml))

  equals :: (LatticeMember l)
         => Key m l -> Key m l -> m (Key m l)

  subsumes :: (LatticeMember l)
           => Key m l
