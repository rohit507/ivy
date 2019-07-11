
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
type ETID = ETermID


instance Newtype ETermID Int where
  pack = ETID
  unpack = getETID

-- | an identifier for a specific term.
newtype TermID t = TID { getTID :: Int }

instance Newtype (TermID t) Int where
  pack = TID
  unpack = getTID

-- | an identifier for a specific term.
newtype VarID t m = VID { getVID :: Int}

instance Newtype (VarID t m) Int where
  pack = VID
  unpack = getVID
