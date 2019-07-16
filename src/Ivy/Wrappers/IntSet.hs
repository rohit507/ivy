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

module Ivy.Wrappers.IntSet where

import Ivy.Prelude hiding (IntSet)
import qualified Data.IntSet as IS

newtype IntSet v = ISW { getIntSet :: IS.IntSet }

deriving newtype instance Semigroup (IntSet v)

type N i = Newtype i Int

empty :: Newtype i Int => IntSet i
empty = ISW IS.empty

singleton :: N i => i -> IntSet i
singleton = ISW . IS.singleton . unpack
