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
import Data.Monoid
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
