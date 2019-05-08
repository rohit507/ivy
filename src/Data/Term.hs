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

data RTerm l k where
  T :: l (RTerm l k) -> RTerm l k
  V :: k -> RTerm l k

deriving instance (Functor l) => Functor (RTerm l)
