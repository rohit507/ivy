
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveAnyClass #-}

{-|
Module      : SudokuSpec
Description : Solves Sudoku by explicitly tracking ambiguity.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

-}

module Ivy.Testing where


import Intro hiding (Item)
import Hedgehog hiding (Var,Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
-- import Ivy.Prelude
import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.IntBindT
import Ivy.ErrorClasses

instance (MonadBind e m t) => MonadBind e (PropertyT m) t where
  type Var (PropertyT m) = Var m
  freeVar = lift freeVar
  lookupVar a = lift $ lookupVar a
  bindVar a t = lift $ bindVar a t
  redirectVar a b = lift $ redirectVar a b
  freshenVar a = lift $ freshenVar a

instance (forall t. MonadBind e (PropertyT m) t => MonadBind e m t
         , MonadProperty e p m)
         => MonadProperty e p (PropertyT m) where

  propertyOf :: forall t t'. (MonadBind e (PropertyT m) t, MonadBind e (PropertyT m) t', Property p t t')
      => p -> Var m t -> PropertyT m (Var m t')
  propertyOf a t = lift $ propertyOf @e a t
