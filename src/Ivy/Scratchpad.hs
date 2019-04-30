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

import Data.Coerce

class (Monad m) => MonadLat m where

  type IsLatErr m :: * -> Constraint

  top :: (IsLatErr m e) => e -> m a
  default top :: (MonadError e m, IsLatErr m e) => e -> m a
  top = throwError

  val :: a -> m a
  default val :: (Monad m) => a -> m a
  val = pure

  bot :: m a
  default bot :: (MonadPlus m) => m a
  bot = empty

data LTerm l k where
  T :: l (LTerm l k) -> LTerm l k
  V :: k -> LTerm l k

class POrd l where

  lessThanOrEq :: (MonadLat m) => l -> l -> m Bool

  lessThan :: (MonadLat m) => l -> l -> m Bool

  greaterThanOrEq :: (MonadLat m) => l -> l -> m Bool

  greaterThan :: (MonadLat m) => l -> l -> m Bool

  equalTo :: (MonadLat m) => l -> l -> m Bool

  notEqualTo :: (MonadLat m) => l -> l -> m Bool

class Lattice l where

  latBottom :: l

  latJoin :: (MonadLat m) => l -> l -> m l

  latMeet :: (MonadLat m) => l -> l -> m l

class POrd1 l where

  liftLessThanOrEq :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m Bool

  liftLessThan :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m Bool

  liftGreaterThanOrEq :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m Bool

  liftGreaterThan :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m Bool

  liftEqualTo :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m Bool

  liftNotEqualTo :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m Bool

class (Functor l) => LatticeF l where

  liftLatBottom :: p -> l p

  liftLatJoin :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m (l p)

  liftLatMeet :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m (l p)

{-
class (Functor (l k)) => LatticeKF k l where

  liftLatBottomWithKey :: p -> l k p

  liftLatJoinWithKey :: (MonadLat m, Lattice p) => (p -> p -> m p) -> l k p -> l k p -> m (l k p)

  liftLatMeetWithKey :: (MonadLat m, Lattice p) => (p -> p -> m p) -> l k p -> l k p -> m (l k p)
-}

infixr 0 :-^

data a :-^ b where

  UCFInt ::(Lattice a, Lattice b) =>
    (forall m. (MonadLat m) => a -> m b) -> a :-^ b

  UCFId :: (a ~ b) => a :-^ b

getUCF :: (Lattice a, Lattice b) => (a :-^ b) -> (forall m. MonadLat m => a -> m b)
getUCF (UCFInt a) = a
getUCF UCFId = pure

instance Category (:-^) where
  id = UCFId

  UCFId . a = a
  a . UCFId = a
  (UCFInt a) . (UCFInt b) = UCFInt (b >=> a)

pattern UCF :: (Lattice a, Lattice b) => (forall m. MonadLat m => a -> m b) -> a :-^ b
pattern UCF f <- (getUCF -> f)
  where
    UCF f = UCFInt f

{-
class (Monad m) => MonadLatticeMap m where

  data Key m l :: *

  bindLat  :: (Lattice l) => Key m l -> l -> m (Key m l)

  getLat   :: (Lattice l) => Key m l -> m l

  -- keys are merged and values are joined
  equals   :: (Lattice l) => Key m l -> Key m l -> m (Key m l)

  subsumes :: (Lattice l) => Key m l -> Key m l -> m Bool
-}

class (Monad m) => MonadLatticeMapF m where

  data KeyF m (l :: * -> *) :: *

  putLatF  :: (LatticeF l) => LTerm l (KeyF m l) -> m (KeyF m l)

  bindLatF  :: (LatticeF l) => KeyF m l -> LTerm l (KeyF m l) -> m (KeyF m l)

  getLatF   :: (LatticeF l) => KeyF m l -> m (LTerm l (KeyF m l))

  equalsF   :: (LatticeF l) => KeyF m l -> KeyF m l -> m (KeyF m l)

  subsumesF :: (LatticeF l) => KeyF m l -> KeyF m l -> m Bool

-- | This is a list of changes to the map that we might be able to apply if
--   neccesary.
data Edit k l
  = Bind (k l) (LTerm l (k l))
  | Equals (k l) (k l)
  | Subsumes (k l) (k l)

-- | As we execute an op over our system, we should be producing transactions as an
--   intermediate state, which allows us to chop things up as neccesary
data Trans k a where

  Parallel:: [Trans k a] -> Trans k a
  Watch :: k a -> (k a -> a -> Trans k b) -> Trans k b
  Run :: [Edit k l] -> Trans k () -> Trans k ()
  Done :: Trans k ()
  Hold :: Trans k ()

{-
-- | Do we ever need to allow the type parameter to be different here?
--   basically I want some way to take sets of keys
class (Monad m) => MonadLatticeMapKF m where

  data KeyKF m (l :: * -> * -> *) :: *

  bindLatKF  :: (LatticeKF (KeyKF m l) l)
    => KeyKF m l -> l (KeyKF m l) (KeyKF m l) -> m (KeyKF m l)

  getLatKF   :: (LatticeKF (KeyKF m l) l)
    => KeyKF m l -> m (l (KeyKF m l) (KeyKF m l))

  -- keys are merged and values are joined
  equalsKF   :: (LatticeKF (KeyKF m l) l)
    => KeyKF m l -> KeyKF m l -> m (KeyKF m l)

  subsumesKF :: (LatticeKF (KeyKF m l) l)
    => KeyKF m l -> KeyKF m l -> m Bool
-}

{-
uAnd :: MonadLatticeProp m => Lat Bool -> Lat Bool -> Lat Bool
uAnd a b = fall a <|> fall b <|> base

  where

    fall :: m Bool -> m Bool
    fall = undefined

    base :: m Bool
    base = (&&) <$> a <$> b

uOr :: MonadLatticeProp m => Lat Bool -> Lat Bool -> Lat Bool
uOr a b = fall a <|> fall b <|> base

  where

    fall :: m Bool -> m Bool
    fall b = undefined

    base :: m Bool
    base = (||) <$> a <$> b

-}
