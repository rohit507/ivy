
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
-- import qualified Hedgehog as H
-- import qualified Hedgehog.Gen as Gen
-- import Ivy.Prelude
-- import Algebra.Lattice
import Ivy.MonadClasses
-- import Ivy.IntBindT
-- import Ivy.ErrorClasses

instance (MonadBind e m t) => MonadBind e (PropertyT m) t where
  type Var (PropertyT m) = Var m
  freeVar = lift freeVar
  lookupVar a = lift $ lookupVar a
  bindVar a t = lift $ bindVar a t
  redirectVar a b = lift $ redirectVar a b
  freshenVar a = lift $ freshenVar a

instance (MonadProperty e p m)
         => MonadProperty e p (PropertyT m) where

  propertyOf :: p -> Var m (From p) -> PropertyT m (Var m (To p))
  propertyOf a t = lift $ propertyOf @e @p a t


-- class ( , MonadError e m
--       , MonadError e (Rule m)
--       , MonadRule e m
--       , Var m ~ Var (Rule m)
--       , Rule (Rule m) ~ (Rule m)
--       ) => MonadRule e m | m -> e where

--   type Rule m :: Type -> Type

--   -- | Default implementation exists for r ~ m, where addRule is just identity.
--   --   since any recursively defined rules should just become a single
--   --   larger rule.
--   addRule :: Rule m () -> m ()
--   default addRule :: (Rule m ~ m) => Rule m () -> m ()
--   addRule = id

--   addGeneralRule :: (MonadBind e m t) => (t (Var m t) -> Rule m ()) -> m ()
