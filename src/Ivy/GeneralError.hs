{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.GeneralError where

import Ivy.Prelude
import Ivy.Wrappers.IDs
import Ivy.MonadClasses



throwInvalidTypeFound :: (InternalError e, MonadError e m, Typeable a, Typeable b) => TypeRep a -> TypeRep b -> m c
throwInvalidTypeFound a b = throwError $ invalidTypeFound a b

throwNonexistentTerm :: (InternalError e, MonadError e m, Typeable t, Typeable m, Typeable m') => Var t m' -> m c
throwNonexistentTerm a = throwError $ nonexistentTerm a

data IntErr e where
  InvalidTypeFound      :: (Typeable a, Typeable b) => TypeRep a -> TypeRep b -> e -> IntErr e
  GettingTermStateFor   :: (Typeable t, Typeable m) => Var t m -> ErrorContext e -> IntErr e
  GettingTerminalVarFor :: (Typeable t, Typeable m) => Var t m -> ErrorContext e -> IntErr e
