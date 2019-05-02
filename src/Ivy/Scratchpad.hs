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
import Data.Monoid
import qualified GHC.Base as Base (mzero, mplus)

class (Alternative m, Monad m) => MonadLat m where

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

data Lat e a where
  Top :: e -> Lat e a
  Val :: a -> Lat e a
  Bot :: Lat e a

deriving instance Functor (Lat e)

instance Semigroup e => Applicative (Lat e) where
  pure = Val

  Top e <*> Top e' = Top $ e <> e'
  Top e <*> _      = Top e
  _     <*> Top e  = Top e
  Val f <*> Val a  = Val $ f a
  Bot   <*> _      = Bot
  _     <*> Bot    = Bot

instance Semigroup e => Alternative (Lat e) where
  empty = Bot
  Bot   <|> a      = a
  a     <|> Bot    = a
  Val a <|> _      = Val a
  _     <|> Val a  = Val a
  Top e <|> Top e' = Top $ e <> e'

instance Semigroup e => Monad (Lat e) where
  Bot   >>= _ = Bot
  Val a >>= f = f a
  Top e >>= _ = Top e

instance Semigroup e => MonadError e (Lat e) where
  throwError = Top
  catchError (Top e) f = f e
  catchError a       _ = a

instance Semigroup e => MonadPlus (Lat e) where
  mzero = Bot
  mplus = (<|>)

data LTerm l k where
  T :: l (LTerm l k) -> LTerm l k
  V :: k -> LTerm l k

deriving instance (Functor l) => Functor (LTerm l)

class POrd l where

  lessThanOrEq    :: l -> l -> Bool
  lessThan        :: l -> l -> Bool
  greaterThanOrEq :: l -> l -> Bool
  greaterThan     :: l -> l -> Bool
  equalTo         :: l -> l -> Bool
  notEqualTo      :: l -> l -> Bool

class (POrd l) => Lattice l where
  latBottom :: l
  latJoin :: (MonadLat m) => l -> l -> m l
  latMeet :: (MonadLat m) => l -> l -> m l

class (Functor l) => POrdF l where

  liftLessThanOrEq    :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftLessThan        :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftGreaterThanOrEq :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftGreaterThan     :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftEqualTo         :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool
  liftNotEqualTo      :: (Monad m) => (p -> p -> m Bool) -> l p -> l p -> m Bool

class (POrdF l) => LatticeF l where
  liftLatBottom :: p -> l p
  liftLatJoin   :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m (l p)
  liftLatMeet   :: (MonadLat m) => (p -> p -> m p) -> l p -> l p -> m (l p)

{-
class (Functor (l k)) => LatticeKF k l where

  liftLatBottomWithKey :: p -> l k
  liftLatJoinWithKey :: (MonadLat m) => (p -> p -> m p) -> l k p -> l k p -> m (l k p)
  liftLatMeetWithKey :: (MonadLat m) => (p -> p -> m p) -> l k p -> l k p -> m (l k p)
-}

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

{-
class (Monad m) => MonadLatticeMap m where

  data Key m l :: *

  bindLat  :: (Lattice l) => Key m l -> l -> m (Key m l)

  getLat   :: (Lattice l) => Key m l -> m l

  -- keys are merged and values are joined
  equals   :: (Lattice l) => Key m l -> Key m l -> m (Key m l)

  subsumes :: (Lattice l) => Key m l -> Key m l -> m Bool
-}

class (Monad m, LatticeF l) => MonadLatMapF m l where

  data KeyF m (l :: * -> *) :: *

  putLatF  :: LTerm l (KeyF m l) -> m (KeyF m l)

  bindLatF  :: KeyF m l -> LTerm l (KeyF m l) -> m (KeyF m l)

  getLatF   :: KeyF m l -> m (LTerm l (KeyF m l))

  equalsF   :: KeyF m l -> KeyF m l -> m (KeyF m l)

  subsumesF ::  KeyF m l -> KeyF m l -> m Bool

-- | An edit captures a single concrete change we could make to our
--   lattice map.
--
--   TODO :: Stuff like adding new terms in our parent language when we implement
--          them.
data Edit m k where

  Put :: (MonadLatMapF m l) => LTerm l k -> Edit m k

  Bind :: (MonadLatMapF m l) => k -> LTerm l k -> Edit m k

  Equals :: k -> k -> Edit m k

  Subsumes :: k -> k -> Edit m k

deriving instance Functor (Edit m)


-- | A Transaction is a suspended computation over the map of terms. When
--   it suspends it could be:
--
--     - A set of hooks which can generate a bunch of transactions when a
--       key is modified.
--
--     - A set of concrete edits to the LatMap we can (presumably) analyse as
--       needed.
--
--     - A signal that this specific transaction is finished, and can be
--       discarded when we finish,
data Transaction m k where

  -- | This transaction will add hooks that trigger when specific lattice
  --   elements are updated.
  Watch :: HashMap k (k -> m (Transaction m k)) -> Transaction m k

  -- | This transaction represents a series of concrete operations that
  --   we can perform on a set of lattice elements, and the transaction that
  --   happens when we
  Run :: F (Edit m) ()  -> Transaction m k

instance (Eq k, Hashable k, Alternative m) => Semigroup (Transaction m k) where

  -- NOTE :: We use the Semigroup instance of `Alt` (in Data.Monoid) to allow the
  -- semigroup instance of HashMap to work over the transactions we return.
  -- With the appropriate choice of alternative instance (`Compose [] Lat`?)
  -- we should be able to extract a list of all the new transactions that were
  -- created.
  --
  -- The big problem here is with duplication of rules. If a rule creates
  -- another rule, should we delete the first?
  --
  -- In the case where create different rules based on what a particular
  -- variable resolves to. Well, it should be an upwards closed function that
  -- differentiates between cases so if one choice is taken the other shouldn't
  -- be.
  --
  -- I guess the case that's weird is if the created rules aren't a flat lattice,
  -- instead becoming something else yet. We might need to keep track of child
  -- rules as we run (each parent rule should have at most one child per object?)
  --
  (Watch m) <> (Watch m') = Watch . unAlt $ wrapAlt m <> wrapAlt m'
    where
      wrapAlt :: HashMap k (k -> m r) -> HashMap k (k -> Alt m r)
      wrapAlt = map (map Alt)

      unAlt :: HashMap k (k -> Alt m r) -> HashMap k (k -> m r)
      unAlt = map (map getAlt)

  -- When we have just have two free monads of edits we can concat them to get
  -- the resulting output.
  (Run f) <> (Run f') = undefined -- Run $ f >> f'

  -- If we have a run and a watch, we watch on the relevant variables and
  -- append the potential side-effects together. Done this way, if we
  -- can create a sandbox for the edit operation, we can run an operation
  -- inside the sandbox and only commit them if certain conditions are met.
  -- (Hmm, flattened sandboxes == provenance == predicated operations. Just
  --  add an interpretation function that will turn a forall into a rule.)
  -- Making decisions with provenance seems like a bad idea.
  Run e   <> Watch m = Watch . map (\ fk k -> (Run e <>) <$> fk k) $ m
  Watch m <> Run e   = Watch . map (\ fk k -> (Run e <>) <$> fk k) $ m


instance (Eq k, Hashable k, Alternative m) => Monoid (Transaction m k) where
  mempty = undefined



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
