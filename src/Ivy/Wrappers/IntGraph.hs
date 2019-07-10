
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

module Ivy.Wrappers.IntGraph where

import Ivy.Prelude
import qualified Algebra.Graph.AdjacencyIntMap as G

newtype IntGraph k = IG { getIntGraph :: G.AdjacencyIntMap }
