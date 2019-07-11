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


-- | A context for an error modifies an error to add additional metadata.
type ErrorContext e = e -> e

-- | Errors that are internal to our current library and are not due to
--   user error.
class InternalError e where
  invalidTypeFound :: (Typeable a, Typeable b) => TypeRep a -> TypeRep b -> e
  nonexistentTerm :: (Typeable t, Typeable m) => Var t m -> e
  gettingTermStateFor :: (Typeable t, Typeable m) => Var t m -> ErrorContext e
  settingTermStateFor :: (Typeable t, Typeable m) => Var t m -> ErrorContext e
  gettingTerminalVarFor :: (Typeable t, Typeable m) => Var t m -> ErrorContext e

throwInvalidTypeFound :: (InternalError e, MonadError e m, Typeable a, Typeable b) => TypeRep a -> TypeRep b -> m c
throwInvalidTypeFound a b = throwError $ invalidTypeFound a b

throwNonexistentTerm :: (InternalError e, MonadError e m, Typeable t, Typeable m, Typeable m') => Var t m' -> m c
throwNonexistentTerm a = throwError $ nonexistentTerm a

data IntErr e where
  InvalidTypeFound      :: (Typeable a, Typeable b) => TypeRep a -> TypeRep b -> e -> IntErr e
  GettingTermStateFor   :: (Typeable t, Typeable m) => Var t m -> ErrorContext e -> IntErr e
  GettingTerminalVarFor :: (Typeable t, Typeable m) => Var t m -> ErrorContext e -> IntErr e
