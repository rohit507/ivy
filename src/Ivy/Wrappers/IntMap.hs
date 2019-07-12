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

module Ivy.Wrappers.IntMap where

import Ivy.Prelude hiding (IntMap)
import qualified Data.IntMap as IM

newtype IntMap k v = IMW { getIntMap :: IM.IntMap v }

type N k = Newtype k Int

empty :: (Newtype k Int) => IntMap k v
empty = IMW IM.empty

singleton :: (N k) => k -> v -> IntMap k v
singleton k = IMW . IM.singleton (unpack k)

lookup :: (N k) => k -> IntMap k v -> Maybe v
lookup k (IMW i) = IM.lookup (unpack k) i

insert :: (N k) => k -> v -> IntMap k v -> IntMap k v
insert k v (IMW i) = IMW $ IM.insert (unpack k) v i

adjust :: (N k) => (v -> v) -> k -> IntMap k v -> IntMap k v
adjust f k (IMW i) = IMW $ IM.adjust f (unpack k) i
