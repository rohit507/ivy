
{-# LANGUAGE AllowAmbiguousTypes #-}
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

module HuttonSpec where

import Intro hiding (Item)
import Hedgehog hiding (Var, Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Control.Concurrent.Supply
import Control.Monad.Morph
import Ivy.Prelude
import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.IntBindT
import Ivy.ErrorClasses
import Ivy.Testing ()
import Internal.IntBindT

newtype ConstF a f where
  ConstF :: a -> ConstF a f

deriving stock instance (Show a) => Show (ConstF a f)
deriving instance Functor (ConstF a)
deriving instance Foldable (ConstF a)
deriving instance Traversable (ConstF a)
deriving newtype instance Num a => Num (ConstF a f)

deriving newtype instance (Eq a) => Eq (ConstF a f)

instance (Eq a, EqualityErr e a) => JoinSemiLattice1 e (ConstF a) where
  liftLatJoin (ConstF a) (ConstF b)
    | a == b = Right $ ConstF a
    | otherwise = Left $ valuesNotEqual a b

newtype MinF a f where
  MinF :: a -> MinF a f

deriving stock instance (Show a) => Show (MinF a f)
deriving instance Functor (MinF a)
deriving instance Foldable (MinF a)
deriving instance Traversable (MinF a)
deriving newtype instance (Eq a) => Eq (MinF a f)
deriving newtype instance (Ord a) => Ord (MinF a f)

instance (Ord a) => JoinSemiLattice1 e (MinF a) where
  liftLatJoin (MinF a) (MinF b) = Right . MinF $ min a b

data HuttonF (a :: Type) (f :: Type) where
  (:+) :: f -> f -> HuttonF a f
  HVal :: a -> HuttonF a f

deriving stock instance (Show a, Show f) => Show (HuttonF a f)
deriving instance Functor (HuttonF a)
deriving instance Foldable (HuttonF a)
deriving instance Traversable (HuttonF a)
deriving instance (Eq a, Eq f) => Eq (HuttonF a f)

instance Eq a => Eq1 (HuttonF a) where
  liftEq eq (a :+ b) (a' :+ b') =  (eq a a') && (eq b b')
  liftEq _ (HVal a) (HVal b) = a == b
  liftEq _ _ _ = False

instance (Num a, Show a, NonUnifiableErr e a) => JoinSemiLattice1 e (HuttonF a) where
  liftLatJoin (a :+ b) (a' :+ b') = Right $ (These a a') :+ (These b b')
  liftLatJoin (HVal a) (HVal b) = Right $ HVal (a + b)
  liftLatJoin a b = Left $ termsNotUnifiable a b

instance (Typeable a) => Property (Min a) where
  type From (Min a) = HuttonF a
  type To (Min a) = MinF a
  rep = Min undefined

data ConstProp (a :: Type) = ConstProp

instance (Typeable a) => Property (ConstProp a) where
  type From (ConstProp a) = HuttonF a
  type To (ConstProp a) = ConstF a
  rep = ConstProp
