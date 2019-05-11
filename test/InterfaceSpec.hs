{-|
Module      : InterfaceSpec
Description : Specifications/tests for various interface properties.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

-}

module InterfaceSpec where

import Ivy.Prelude
import Control.Monad.Lat.Class
import Control.Monad.Prop.Class
import Control.Monad.TermGraph.Class


-- | Hutton's Razor expressed as a datatype.
data HuttonF f where
  I :: Int -> HuttonF f
  P :: f -> f -> HuttonF f

-- | Okay, this assumes that the lattice for Int is flat. And this only
--   assumes single level term unrolling. The larger scale unrolling can
--   be done in some other context (presumably)
evalHutton :: (MonadTermGraph m, MonadProp m) => Vert m -> m ()
evalHutton v = undefined
{- evalHutton v = getTerm v >>= \case
  v := I n -> do
    k <- getKey @Int n
    bindLat k n
  v := P a b -> do
    ka <- getKey @Int a
    kb <- getKey @Int b
    kv <- getKey @Int v
    a <- getLat ka
    b <- getLat kb
    bindLat kb (a + b)
  _ -> pure ()
-}


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
