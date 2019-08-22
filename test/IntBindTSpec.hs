{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : SudokuSpec
Description : Solves Sudoku by explicitly tracking ambiguity.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

-}

module IntBindTSpec where

import Intro hiding (Item)
import Hedgehog
import qualified Hedgehog.Gen as Gen
import Ivy.Prelude
import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.IntBindT

-- TODO :: Basic Test Cases to ensure that propagation, subsumption, and other
--         key operations are valid.
--
--   -- Terms :: Free, Lookup, Bind, Redirect, Freshen?
--   -- Properties
--   -- Rule
--   -- Default Rule
--   -- Equals
--   -- Unification
--   -- Subsumption
