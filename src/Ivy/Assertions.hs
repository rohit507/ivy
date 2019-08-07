{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.Assertions where

import Ivy.Prelude hiding (IntSet, IntMap)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Partition (Partition)
import qualified Data.Partition as P

-- | A set of assertions on terms that we can use to prevent loops and the like
data Assertions a = Assertions
  { _equalities   :: Partition a
  , _unifications :: Partition a
  , _subsumptions :: HashMap a (HashSet a)
  }

makeFieldsNoPrefix ''Assertions

instance (Ord a, Hashable a) => Semigroup (Assertions a) where
  (Assertions e u s) <> (Assertions e' u' s')
    = updateSubs $ Assertions {
      _equalities   = P.fromSets $ P.nontrivialSets e <> P.nontrivialSets e'
    , _unifications = P.fromSets $ P.nontrivialSets u <> P.nontrivialSets u'
    , _subsumptions = HM.unionWith (<>) s s'
    }

instance (Ord a, Hashable a) => Monoid (Assertions a) where
 mempty = Assertions P.empty P.empty mempty

getRep :: (Ord i) => i -> Assertions i -> i
getRep i a = P.rep (a ^. unifications) i
{-# INLINE getRep #-}

getRepL :: (Ord i) => i -> [Assertions i] -> i
getRepL i [] = i
getRepL i (l:ls) = getRepL (getRep i l) ls


addEqAssertion :: (Ord i) => i -> i -> Assertions i -> Assertions i
addEqAssertion a b = equalities %~ P.joinElems a b

addSubAssertion :: (Ord i, Hashable i) => i -> i -> Assertions i -> Assertions i
addSubAssertion a b = subsumptions %~ HM.insertWith (<>) a (HS.singleton b)

addUniAssertion :: (Ord i, Hashable i) => i -> i -> Assertions i -> Assertions i
addUniAssertion a b = updateSub a b . addEqAssertion a b . (unifications %~ P.joinElems a b)

updateSubs :: (Ord i, Hashable i) => Assertions i -> Assertions i
updateSubs a@Assertions{..} = a{
    _subsumptions = HM.fromListWith (<>) $ map (\ (i,b) -> (getRep i a,b)) newList
  }
  where
    newList = HM.toList $ map (HS.map (\ i -> getRep i a)) _subsumptions
{-# INLINE updateSubs #-}

updateSub :: (Ord i, Hashable i) => i -> i -> Assertions i -> Assertions i
updateSub i j a = if isAssertedSubsumed j i a
  then addUniAssertion i j a
  else (subsumptions %~
     ( HM.adjust (HS.map (\ n -> if n == i then j else n)) i
     . HM.delete j
     . adjusting)) a
  where
    adjusting = case HM.lookup j (_subsumptions a) of
      Nothing -> id
      Just s  -> HM.insertWith (<>) i s

isAssertedEqual :: (Ord i) => i -> i -> Assertions i -> Bool
isAssertedEqual i j a
  = isAssertedUnified i j a || (   (P.rep (a ^. equalities) (getRep i a))
    == (P.rep (a ^. equalities) (getRep j a)))
{-# INLINE isAssertedEqual #-}

isAssertedEqualL :: (Ord i) => i -> i -> [Assertions i] -> Bool
isAssertedEqualL _ _ [] = False
isAssertedEqualL i j (l:ls) = isAssertedEqual i j l || isAssertedEqualL i' j' ls
  where
    i' = getRep i l
    j' = getRep j l

isAssertedUnified :: (Ord i) => i -> i -> Assertions i -> Bool
isAssertedUnified i j a
  =    (P.rep (a ^. unifications) (getRep i a))
    == (P.rep (a ^. unifications) (getRep j a))
{-# INLINE isAssertedUnified #-}

isAssertedUnifiedL :: (Ord i) => i -> i -> [Assertions i] -> Bool
isAssertedUnifiedL _ _ [] = False
isAssertedUnifiedL i j (l:ls) = isAssertedUnified i j l || isAssertedUnifiedL i' j' ls
  where
    i' = getRep i l
    j' = getRep j l

isAssertedSubsumed :: (Ord i, Hashable i) => i -> i -> Assertions i -> Bool
isAssertedSubsumed i j a = (isAssertedUnified i j a) || (
  case HM.lookup (getRep i a) (a ^. subsumptions) of
    Nothing -> False
    Just b  -> HS.member (getRep j a) b)
{-# INLINE isAssertedSubsumed #-}

isAssertedSubsumedL :: (Ord i, Hashable i) => i -> i -> [Assertions i] -> Bool
isAssertedSubsumedL _ _ [] = False
isAssertedSubsumedL i j a@(l:ls) = isAssertedSubsumed i j l || isAssertedSubsumedL i' j' ls
  where
    i' = getRepL i a
    j' = getRepL j a
{-# INLINE isAssertedSubsumedL #-}
