{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : Data.Lat
Description : The Lat type
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Data.Lat where

import Ivy.Prelude

import Control.Monad.Lat.Class

import Data.POrd
import Data.Lattice

import qualified GHC.Base as Base (mzero, mplus)

data Lat e a where
  Top :: e -> Lat e a
  Val :: a -> Lat e a
  Bot :: Lat e a

deriving instance Functor (Lat e)

instance Semigroup e => Applicative (Lat e) where

  pure = Val

  Top e <*> Top e' = Top $ e <> e'
  Top e <*> _      = Top e
  _     <*> Top e  = Top e
  Val f <*> Val a  = Val $ f a
  Bot   <*> _      = Bot
  _     <*> Bot    = Bot

instance Semigroup e => Alternative (Lat e) where

  empty = Bot
  Bot   <|> a      = a
  a     <|> Bot    = a
  Val a <|> _      = Val a
  _     <|> Val a  = Val a
  Top e <|> Top e' = Top $ e <> e'

instance Semigroup e => Monad (Lat e) where
  Bot   >>= _ = Bot
  Val a >>= f = f a
  Top e >>= _ = Top e

instance Semigroup e => MonadError e (Lat e) where

  throwError = Top

  catchError (Top e) f = f e
  catchError a       _ = a

instance Semigroup e => MonadPlus (Lat e) where
  mzero = Bot
  mplus = (<|>)

instance (Semigroup e) => MonadLat (Lat e) where

  type IsLatErr (Lat e) e' = (e ~ e')

  top = Top
  val = Val
  bot = Bot

instance POrdF (Lat e) where

  liftLessThanOrEq _ _       (Top _) = pure True
  liftLessThanOrEq _ (Top _) _       = pure False
  liftLessThanOrEq _ Bot     _       = pure True
  liftLessThanOrEq _ _       Bot     = pure False
  liftLessThanOrEq f (Val a) (Val b) = f a b

  liftLessThan _ (Top _) (Top _) = pure False
  liftLessThan _ _       (Top _) = pure True
  liftLessThan _ (Top _) _       = pure False
  liftLessThan _ Bot     Bot     = pure False
  liftLessThan _ Bot     _       = pure True
  liftLessThan _ _       Bot     = pure False
  liftLessThan f (Val a) (Val b) = f a b

  liftGreaterThanOrEq _ (Top _) _       = pure True
  liftGreaterThanOrEq _ _       (Top _) = pure False
  liftGreaterThanOrEq _ _       Bot     = pure True
  liftGreaterThanOrEq _ Bot     _       = pure False
  liftGreaterThanOrEq f (Val a) (Val b) = f a b

  liftGreaterThan _ (Top _) (Top _) = pure False
  liftGreaterThan _ (Top _) _       = pure True
  liftGreaterThan _ _       (Top _) = pure False
  liftGreaterThan _ Bot     Bot     = pure False
  liftGreaterThan _ _       Bot     = pure True
  liftGreaterThan _ Bot     _       = pure False
  liftGreaterThan f (Val a) (Val b) = f a b

  liftEqualTo _ (Top _) (Top _) = pure True
  liftEqualTo _ Bot     Bot     = pure True
  liftEqualTo f (Val a) (Val b) = f a b
  liftEqualTo _ _       _       = pure False

  liftNotEqualTo _ (Top _) (Top _) = pure False
  liftNotEqualTo _ Bot     Bot     = pure False
  liftNotEqualTo f (Val a) (Val b) = f a b
  liftNotEqualTo _ _       _       = pure True

instance (POrd v) => Eq (Lat e v) where
  (==) = dropEQ
  (/=) = dropNEQ

instance (POrd v) => POrd (Lat e v) where
  lessThanOrEq    = dropLTE
  lessThan        = dropLT
  greaterThanOrEq = dropGTE
  greaterThan     = dropGT

instance (Semigroup e) => LatticeF (Lat e) where
  -- liftLatBottom _ = Bot

  liftLatJoin _ (Top e) (Top e') = pure . Top $ e <> e'
  liftLatJoin _ e@(Top _) _ = pure e
  liftLatJoin _ _ e@(Top _) = pure e
  liftLatJoin _ Bot a = pure a
  liftLatJoin _ a Bot = pure a
  liftLatJoin f (Val a) (Val b) = Val <$> f a b

  liftLatMeet _ Bot _ = pure Bot
  liftLatMeet _ _ Bot = pure Bot
  liftLatMeet _ (Top _) a = pure a
  liftLatMeet _ a (Top _) = pure a
  liftLatMeet f (Val a) (Val b) = Val <$> f a b

instance (Semigroup e, Lattice v) => Lattice (Lat e v) where

  type LatErr m (Lat e v) = (LatErrF m (Lat e) v, LatErr m v)
  -- latBottom = dropBot
  latJoin   = dropJoin
  latMeet   = dropMeet
