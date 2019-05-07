{-|
Module      : Data.Term
Description : Types for working with fixed point representations of grammars.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Data.Term where

import Ivy.Prelude

data LTerm l k where
  T :: l (LTerm l k) -> LTerm l k
  V :: k -> LTerm l k

deriving instance (Functor l) => Functor (LTerm l)
