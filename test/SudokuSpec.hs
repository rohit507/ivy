{-|
Module      : SudokuSpec
Description : Solves Sudoku by explicitly tracking ambiguity.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

-}

module SudokuSpec where

import Ivy.Prelude
import Control.Monad.Lat.Class
import Control.Monad.Prop.Class
import Control.Monad.TermGraph.Class

import Data.Lattice
import qualified Data.IntSet as IntSet

-- | Set of potential options for each value in the grid.
data Options = Opts IntSet

instance Lattice Options where

  latJoin (Opts a) (Opts b) = if
    | IntSet.null c = top "There are no valid options for this square."
    | otherwise = val $ Opts c
    where
      c = IntSet.intersection a b

  latMeet (Opts a) (Opts b) = if
    | IntSet.fromList [1..9] == c = bottom
    | otherwise = val $ Opts c
    where
      c = IntSet.union a b


newtype Fixed = Fixed Int

-- | A set of values that must be unique
data Group a = Grp [a]

-- TODO ::
--
--   - Define lattice instance for Options
--   - Define a rule for a group
--     -- get all consts in group, all options are grp - consts.
--
--   - W/in initial tests
--     -- create 81 verts
--     -- associate each group of verts
--     -- assign values to verts and see how those propagate as we tell
--        the system to quiesce
--     -- Test that it can catch broken assignments.
--
--   - W/in later tests
--     -- Add rule w/ only triggers when quiesced and unsolved
--        -- picks a random assignment for an ambiguous value
--        -- creates shadow network w/ that value assigned
--           -- if errors on quiesce then remove from options.
--           -- if sucessful sets all terms in parent network.
--           -- don't do anything on partial, just wait.
--
-- NOTE :: Doing this properly probably means we should have some notion
--        of task priorities and running hooks in some priority order.
