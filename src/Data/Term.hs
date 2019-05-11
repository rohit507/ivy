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

-- NOTE :: Maybe with the stuff from the following link it should be possible
--        to usefully unwrap RTerm and provide a nice pattern synonym that
--        allows us to write patterns of l for values of RTerm (Base l) k
--        and keep track of whether a match is over or underapproximated.
--
-- http://mpickering.github.io/posts/2014-11-27-pain-free.html
--
-- import Data.Functor.Foldable

data RTerm l k where
  T :: l (RTerm l k) -> RTerm l k
  V :: k -> RTerm l k

deriving instance (Functor l) => Functor (RTerm l)

-- I want to be able to translate:
--
--    Fx (v := (a :+ b) :* c) <- get f
--    ...
--
-- Into
--
--   v :=$ a <- get f
--   e :*$ c <- get a
--   a :+$ b <- get e
--   ...
--
--  so I want something like
--
--    pattern Fx :: a -> m (Key a)
--
--  Fx a <- (bind -> Just a)
--
--  Fuck it, I don't know, I should come back to this later.
