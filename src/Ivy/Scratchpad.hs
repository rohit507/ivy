{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.Scratchpad where

import Ivy.Prelude
import Control.Monad.Lat.Class



-- * Sadly, without some way to introspect whether a term is forced, we can't
--   have the nicer interface which allows us to write more or less pure
--   functions and have their fall-through properties inferred.
--   instead we use the lesser of two evils and work with the lattice elements
--   more directly.

-- | This definition of And is a race between three separate result conditions
--   the two fallthrough cases if a or b are false, and the completed case when
--   both are true.
uAnd :: (MonadLat m) => m Bool -> m Bool -> m Bool
uAnd a b = (a >>= fall) <|> (b >>= fall) <|> ((&&) <$> a <*> b)

  where

    fall False = val False
    fall True  = bot


uOr :: (MonadLat m) => m Bool -> m Bool -> m Bool
uOr a b = (a >>= fall) <|> (b >>= fall) <|> ((&&) <$> a <*> b)

  where

    fall True  = val True
    fall False = bot
