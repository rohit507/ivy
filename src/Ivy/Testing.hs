
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
import Ivy.Prelude
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

instance (MonadAssume e m t) => MonadAssume e (PropertyT m) t where

  assumeEqual a b = hoist $ assumeEqual a b
  assumeUnified a b = hoist $ assumeUnified a b
  assumeSubsumed a b = hoist $ assumeSubsumed a b
  assertEqual a b = lift $ assertEqual a b
  assertUnified a b = lift $ assertUnified a b
  assertSubsumed a b = lift $ assertSubsumed a b
  isAssumedEqual a b = lift $ isAssumedEqual a b
  isAssumedUnified a b = lift $ isAssumedUnified a b
  isAssumedSubsumed a b = lift $ isAssumedSubsumed a b

instance (MonadProperties e m
         , Monad m
         , Var m ~ Var (PropertyT m)
         , forall t. MonadBind e (PropertyT m) t => MonadBind e m t
         ) => MonadProperties e (PropertyT m) where

  getPropertyPairs :: forall a t. (MonadBind e (PropertyT m) t)
      => (forall proxy p. (From p ~ t
                         , MonadAssume e (PropertyT m) (To p)
                         , MonadProperty e p (PropertyT m)
                         , Property p)
                      => proxy p
                      -> These (Var m (To p)) (Var m (To p)) -> PropertyT m a)
      -> (a -> a -> PropertyT m a)
      -> a
      -> Var m t -> Var m t -> PropertyT m a
  getPropertyPairs f append empty a b = do
    traceM "start getting pairs"
    r <- lift $ getPropertyPairs @e
        (\ p t -> do
            traceM "PropPair 1"
            pure . pure $ f p t)
        (\ a b -> do
            traceM "propPair 2"
            pure $ a <> b)
        [] a b
    traceM "end getting pairs"
    foldrM @[] append empty =<< sequenceA r


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
