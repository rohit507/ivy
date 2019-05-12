{-|
Module      : Data.Transaction
Description : Type of suspended computations over a set of triggers.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

FIXME :: Concept needs better name -_-
-}

module Data.Transaction where

import Ivy.Prelude
import Data.Functor (fmap)

import Control.Monad.Lat.Class
import Control.Monad.LatMap.Class
import Control.Monad.Prop.Class
import Control.Monad.TermGraph.Class
import Control.Monad.Free

import Data.POrd
import Data.Lattice
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.HashMap.Lazy as HashMap

newtype a ~> b = Morph { getMorph :: forall x. a x -> b x }

newtype TransactT s m a where
  TT :: {unTT :: (Edit m ~> Transaction s m) -> Transaction s m a }
    -> TransactT s m a

data Transaction s m a where
  WatchT :: HashMap s (s -> m (TransactT s m a)) -> Transaction s m a
  TopT  :: (MonadError e m) => e -> Transaction s m a
  BotT  :: Transaction s m a
  RunT  :: F (Edit m) a -> Transaction s m a
  LiftT :: m (TransactT s m a) -> Transaction s m a
  ManyT :: [TransactT s m a] -> Transaction s m a

-- | An edit captures a single concrete change we could make to our
--   lattice map.
--
--   When we use this within a free monad we have
data Edit m a where

  AddTerm :: (MonadTermGraph m, TermCons t m)
    => t (Vert m) -> Edit m (Term t m)

  Put      :: (MonadLatMap v m, LatCons m v)
    => LatMemb m v -> Edit m (Key m v)

  Bind     :: (MonadLatMap v m, LatCons m v)
    => Key m v -> LatMemb m v -> Edit m (Key m v)

  Equals   :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m (Key m v)

  Subsumes :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m Bool

instance (Functor m) => Functor (Transaction s m) where
  fmap _ (TopT   e) = TopT e
  fmap _ BotT       = BotT
  fmap f (ManyT  l) = ManyT $ map f <$> l
  fmap f (WatchT m) = WatchT $ (map . map . map . map) f m
  fmap f (RunT   a) = RunT $ map f a
  fmap f (LiftT  a) = LiftT $ fmap f <$> a

instance (Functor m) => Functor (TransactT s m) where
  fmap f (TT fm) = TT (\ s -> f <$> fm s)

instance (Functor m) => Applicative (Transaction s m) where
  pure = RunT . pure

  (<*>) :: Transaction s m (a -> b) -> Transaction s m a -> Transaction s m b
  -- We want errors to be propagated forward as early as possible so that
  -- we don't keep rules hanging around longer than neccesary.
  (TopT e) <*> _ = TopT e
  _ <*> (TopT e) = TopT e
  BotT <*> _ = BotT
  _ <*> BotT = BotT

  -- Many indicates non-determinism of a more general sort, where multiple
  -- different constructors of a TransactT are used in parallel
  (ManyT lf) <*> a = ManyT [TT (\ s -> unTT f s <*> a) | f <- lf]
  f <*> (ManyT la) = ManyT [TT (\ s -> f <*> unTT a s) | a <- la]

  -- If we've got at least one watch parameter then we need to float it
  -- outwards as we continue building the resulting Edit
  (WatchT mf) <*> a = WatchT $ (map . map . map)
    (\ f -> TT (\ s -> unTT f s <*> a)) mf
  f <*> (WatchT ma) = WatchT $ (map . map . map)
    (\ a -> TT (\ s -> f <*> unTT a s)) ma
  -- Otherwise we follow the rules for the free monad.
  (RunT   f ) <*> (RunT   a ) = RunT $ f <*> a

  -- And well, we're just waiting
  (LiftT a) <*> b = LiftT $ (\ (TT sa) -> TT (\ s -> sa s <*> b)) <$> a
  a <*> (LiftT b) = LiftT $ (\ (TT sb) -> TT (\ s -> a <*> sb s)) <$> b

instance (Functor m) => Applicative (TransactT s m) where
  pure a = TT (\ _ -> pure a)

  TT sf <*> TT sa = TT (\ s -> sf s <*> sa s)

instance (Applicative m, Eq s, Hashable s) => Alternative (Transaction s m) where
  empty = BotT

  BotT <|> b = b
  b <|> BotT = b

  (TopT e) <|> _ = TopT e
  _ <|> (TopT e) = TopT e

  WatchT ma <|> WatchT mb = WatchT $ HashMap.unionWith deepAlt ma mb
    where
      deepAlt :: (s -> m (TransactT s m a))
              -> (s -> m (TransactT s m a))
              -> (s -> m (TransactT s m a))
      deepAlt fa fb = \ s -> (<|>) <$> fa s <*> fb s

  a <|> WatchT mb = WatchT $ (map . map . map)
    (\ b -> TT (\ s -> a <|> unTT b s)) mb
  WatchT ma <|> b = WatchT $ (map . map . map)
    (\ a -> TT (\ s -> unTT a s <|> b)) ma

  (ManyT la) <|> (ManyT lb) = ManyT $ la <> lb
  (ManyT la) <|> b = ManyT $ la <> [TT (\ _ -> b)]
  a <|> (ManyT lb) = ManyT $ TT (\ _ -> a) : lb

  LiftT a <|> b = LiftT $ (\ (TT sa) -> TT (\ s -> sa s <|> b)) <$> a
  a <|> LiftT b = LiftT $ (\ (TT sb) -> TT (\ s -> a <|> sb s)) <$> b

  a <|> b = ManyT [TT (\ _ -> a), TT (\ _ -> b)]


instance (Applicative m, Eq s, Hashable s) => Alternative (TransactT s m) where
  empty = TT (\ _ -> empty)

  TT sa <|> TT sb = TT (\ s -> sa s <|> sb s)

instance (Monad m) => Monad (Transaction s m) where
 TopT e >>= _ = TopT e
 BotT >>= _ = BotT
 WatchT ma >>= f = WatchT $ (map . map . map)
   (\ (TT sa) -> TT (\ s -> sa s >>= f )) ma

 LiftT a >>= f = LiftT $ (\ ta -> TT (\ s -> unTT ta s >>= f)) <$> a

 RunT a >>= f = LiftT . pure . TT $ (\ s -> foldF (getMorph s) a >>= f)

instance (Monad m) => Monad (TransactT s m) where
  TT sa >>= f = TT (\ s -> sa s >>= (\ x -> unTT (f x) s))

instance (MonadError e m) => MonadError e (TransactT s m)
instance (MonadError e m) => MonadError e (Transaction s m)

type KeyT s m = Key (Transaction s m)

instance (MonadLatMap v m) => MonadLatMap v (Transaction s m) where
  data Key     (Transaction s m) v = TKey (Key m v)
  type LatMemb (Transaction s m) v = LatMemb m v
  type LatCons (Transaction s m) v = LatCons m v

  putLat   :: (LatCons m v)
    => LatMemb m v
    -> Transaction s m (KeyT s m v)
  putLat = undefined

  getLat   :: (LatCons m v)
    => KeyT s m v
    -> Transaction s m (LatMemb m v)
  getLat = undefined

  bindLat  :: (LatCons m v)
    => KeyT s m v
    -> LatMemb m v
    -> Transaction s m (KeyT s m v)
  bindLat = undefined

  equals   :: (LatCons m v)
    => KeyT s m v
    -> KeyT s m v
    -> Transaction s m (KeyT s m v)
  equals = undefined

  subsumes :: (LatCons m v)
    => KeyT s m v
    -> KeyT s m v
    -> Transaction s m Bool
  subsumes = undefined

instance (MonadTermGraph m) => MonadTermGraph (Transaction s m) where

  type Term t' (Transaction s m) = Term t' m
  type Vert (Transaction s m) = Vert m
  type TermCons t' (Transaction s m) = TermCons t' m

  addTerm :: (TermCons t' m)
    => (t' (Vert (Transacttion s m))) -> Transaction s m (Term t' m)
  addTerm = undefined

  getTerm :: (TermCons t' m) => Term t' m -> Transaction s m (t' (Vert m))
  getTerm = undefined
