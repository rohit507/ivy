
{---# LANGUAGE AllowAmbiguousTypes #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

A pile of instances of `Newtype * Int` that we use to differentiate Idents
used for different purposes.
-}

module Ivy.Wrappers.IDs where

import Ivy.Prelude

-- | A termID without knowledge about the type of its term.
newtype ETermID = ETID { getETID :: Int }
  deriving (Eq, Ord, Show, Generic, Hashable)
type ETID = ETermID


instance Newtype ETermID Int where
  pack = ETID
  unpack = getETID

-- | an identifier for a specific term.
newtype TermID t = TID { getTID :: Int }
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Newtype (TermID t) Int where
  pack = TID
  unpack = getTID

type TID = TermID

-- | an identifier for a specific term.
newtype VarID t m = VID { getVID :: Int}
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Newtype (VarID t m) Int where
  pack = VID
  unpack = getVID

newtype RuleID = RID { getRID :: Int}
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Newtype RuleID Int where
  pack = RID
  unpack = getRID

-- | Strip type information from a TermID
crushTID :: TermID t -> ETermID
crushTID = pack . unpack

-- | Add (potentially incorrect) type information to am ETID
unsafeExpandTID :: ETermID -> TermID t
unsafeExpandTID = pack . unpack

-- | Strip Monad information from a VerID
crushVID :: VarID t m -> TermID t
crushVID = pack . unpack

flattenVID :: VarID t m -> ETID
flattenVID = crushTID . crushVID

-- | Add (potentially incorrect) monad information to a VID
unsafeExpandVID :: TermID t -> VarID t m
unsafeExpandVID = pack . unpack
