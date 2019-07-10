{-|
Module      : Ivy.Prelude
Description : The prelude we use throughout this library
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.Prelude (
    module P
) where

import Intro as P
import Type.Reflection as P
import Data.Dynamic as P
import Data.Constraint as P hiding (top)
import Data.Bifoldable as P
import Data.Bitraversable as P
import Data.Functor.Foldable as P hiding (fold)
import Data.Functor.Foldable.TH as P
import Data.Reify as P
import Control.Monad.Free.Church as P
import Control.Newtype as P
import GHC.Exts as P (fromListN)
import GHC.TypeLits as P

{-
import Data.Functor as B

-- | This is a pair type meant mainly for syntax sugar, `key := val` is to be
--   read as "<key> is defined as <val>".
--
--   When bitraversed or bifolded over the value is evaluated before the key.
data a := b = a := b
  deriving(Show, Read, Eq, Ord, Typeable)
infixr 0 :=

instance B.Functor ((:=) a) where
  fmap f (a := b) = a := f b

instance Bifunctor (:=) where
  bimap f g (a := b) = f a := g b
  first f (a := b) = f a := b
  second g (a := b) = a := g b

instance Bifoldable (:=) where
  -- bitmap f g (a := b) = f a <> g b
  bifoldr f g d (a := b) = f a . g b $ d

instance Bitraversable (:=)

-- | This is the version of := where we know that the key has the same type as
--   the elements of the definition.
--
--   When traversed or folded over the value is changed before the key.
data f ::= a = a ::= (f a)
  deriving(Show, Read, Eq, Ord, Typeable)
infixr 0 ::=

instance Functor f => Functor ((::=) f) where
  fmap f (a ::= b) = f a ::= map f b

instance Foldable f => Foldable ((::=) f) where
  foldr f d (a ::= b) = f a (foldr f d b)

instance Traversable f => Traversable ((::=) f) where
  sequenceA (a ::= b) = flip (::=) <$> sequenceA b <*> a
-}
