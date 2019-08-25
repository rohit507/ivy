{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

Main error classes we use in various parts of the system.
-}

module Ivy.ErrorClasses where

import Intro hiding (Item)
-- import Ivy.Prelude

class EqualityErr e a where
  valuesNotEqual :: a -> a -> e

throwValuesNotEqual :: (EqualityErr e a, MonadError e m) => a -> a -> m b
throwValuesNotEqual a b = throwError $ valuesNotEqual a b

instance (Show a) => EqualityErr Text a where
  valuesNotEqual :: a -> a -> Text
  valuesNotEqual a b = "Values `" <> show a <> "`, `" <> show b <> "` are not equal."

instance (Show a) => EqualityErr Void a where
  valuesNotEqual :: a -> a -> Void
  valuesNotEqual a b = panic $ valuesNotEqual a b
