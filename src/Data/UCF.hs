{-|
Module      : Data.UCF
Description : Category of upwards closed functions w/in some partial ordering.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Data.UCF where

import Ivy.Prelude
import Data.Lattice
import Control.Monad.Lat.Class

infixr 0 :-^

-- | This is effectively a constrained category of upwards closed functions.
--   In an ideal world we could perform all of our operations using this category
--   but in practice that's inconvenient and so we
data a :-^ b where

  UCFInt ::(Lattice a, Lattice b) =>
    (forall m. (MonadLat m) => a -> m b) -> a :-^ b

  UCFId :: (a ~ b) => a :-^ b

getUCF :: (Lattice a, Lattice b) => (a :-^ b) -> (forall m. MonadLat m => a -> m b)
getUCF (UCFInt a) = a
getUCF UCFId      = pure

instance Category (:-^) where

  id = UCFId

  UCFId      . a          = a
  a          . UCFId      = a
  (UCFInt a) . (UCFInt b) = UCFInt (b >=> a)

pattern UCF :: (Lattice a, Lattice b) => (forall m. MonadLat m => a -> m b) -> a :-^ b
pattern UCF f <- (getUCF -> f)
  where
    UCF f = UCFInt f
