{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : Data.Transaction
Description : Type of suspended computations over a set of triggers.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

FIXME :: Concept needs better name -_-

FIXME :: A Transaction is some unholy mixture of LatT, FreeT, ReaderT, ListT,
  and quite possibly more besides.

    - Is there some way to decompose it into a transformer stack?
    - If there is, should we?

-}

module Data.Transaction where

import Ivy.Prelude
import Data.Functor (fmap)

import Control.Monad.Lat.Class
import Control.Monad.LatMap.Class
import Control.Monad.PropRule.Class
import Control.Monad.TermGraph.Class
import Control.Monad.Free

import Data.Coerce
import Type.Reflection

import Data.POrd
import Data.Lattice
import qualified Data.IntMap as IntMap
import qualified Data.HashMap.Lazy as HashMap

-- We disable these warnings since actually applying them strips
-- types of the higher order polymorphism that GHC needs to typechecks
{-# ANN module ("HLint: ignore Use const" :: String) #-}
{-# ANN module ("HLint: ignore Use >=>" :: String) #-}
{-# ANN module ("HLint: ignore Use fmap" :: String) #-}

newtype a ~> b = Morph { getMorph :: forall x. a x -> b x }

data Trigger m where
   TKey :: (Eq (Key m v), Hashable (Key m v))
     => TypeRep v -> Key m v -> Trigger m
   TVert :: (Eq (Vert m), Hashable (Vert m))
     => Vert m -> Trigger m

class (Typeable e) => TransactionErr e where
  expectedKeyTrigger  :: (Typeable m) => Trigger m -> e
  expectedVertTrigger :: (Typeable m) => Trigger m -> e
  invalidKeyType :: TypeRep expected -> TypeRep actual -> e

throwExpectedKeyTrigger :: (TransactionErr e, MonadError e m, Typeable m)
                        => Trigger m -> m a
throwExpectedKeyTrigger = throwError . expectedKeyTrigger

throwExpectedVertTrigger :: (TransactionErr e, MonadError e m, Typeable m)
                        => Trigger m -> m a
throwExpectedVertTrigger = throwError . expectedVertTrigger

throwInvalidKeyType :: (TransactionErr e, MonadError e m, Typeable m)
  => TypeRep exp -> TypeRep act -> m a
throwInvalidKeyType a b = throwError $ invalidKeyType a b

instance Eq (Trigger m) where

  TKey ta (a :: Key m a) == TKey tb (b :: Key m b)
    = case eqTypeRep ta tb of
        Nothing -> False
        Just HRefl -> a == b

  TVert a == TVert b = a == b
  _ == _ = False

instance Hashable (Trigger m) where
  hashWithSalt s (TVert v) = hashWithSalt s v
  hashWithSalt s (TKey tk k) = s `hashWithSalt` tk `hashWithSalt` k

newtype TransactT m a where
  TT :: {unTT :: (Edit m ~> m) -> Transaction m a }
    -> TransactT m a


data Transaction m a where
  WatchT :: HashMap (Trigger m) (Trigger m -> m (TransactT m a)) -> Transaction m a
  TopT  :: (MonadError e m) => e -> Transaction m a
  BotT  :: Transaction m a
  RunT  :: F (Edit m) a -> Transaction m a
  LiftT :: m (TransactT m a) -> Transaction m a
  ManyT :: [TransactT m a] -> Transaction m a

-- | An edit captures a single concrete change we could make to our
--   lattice map.
--
--   When we use this within a free monad we have
data Edit m a where

  AddE      :: (MonadTermGraph m, TermCons t m)
    => t (Vert m) -> Edit m (Term t m)

  PutE      :: (MonadLatMap v m, LatCons m v)
    => LatMemb m v -> Edit m (Key m v)

  BindE     :: (MonadLatMap v m, LatCons m v)
    => Key m v -> LatMemb m v -> Edit m (Key m v)

  EqualsE   :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m (Key m v)

  SubsumesE :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m Bool

  -- | Help, I have no idea what I'm supposed to be doing here.
  MapE :: (a ~ a') => Edit m a -> (a' -> b) -> Edit m b

instance Functor (Edit m) where
  fmap f (MapE a g) = MapE a (f . g)
  fmap f e = MapE e f

instance (Functor m) => Functor (Transaction m) where
  fmap _ (TopT   e) = TopT e
  fmap _ BotT       = BotT
  fmap f (ManyT  l) = ManyT $ map f <$> l
  fmap f (WatchT m) = WatchT $ (map . map . map . map) f m
  fmap f (RunT   a) = RunT $ map f a
  fmap f (LiftT  a) = LiftT $ fmap f <$> a

instance (Functor m) => Functor (TransactT m) where
  fmap f (TT fm) = TT (\ s -> f <$> fm s)

instance (Functor m) => Applicative (Transaction m) where
  pure = RunT . pure

  (<*>) :: Transaction m (a -> b) -> Transaction m a -> Transaction m b
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
  -- Otherwise we follow the rules fWor the free monad.
  (RunT   f ) <*> (RunT   a ) = RunT $ f <*> a

  -- And well, we're just waiting
  (LiftT a) <*> b = LiftT $ (\ (TT sa) -> TT (\ s -> sa s <*> b)) <$> a
  a <*> (LiftT b) = LiftT $ (\ (TT sb) -> TT (\ s -> a <*> sb s)) <$> b

instance (Functor m) => Applicative (TransactT m) where
  pure a = TT (\ _ -> pure a)

  TT sf <*> TT sa = TT (\ s -> sf s <*> sa s)

instance (Applicative m) => Alternative (Transaction m) where
  empty = BotT

  BotT <|> b = b
  b <|> BotT = b

  (TopT e) <|> _ = TopT e
  _ <|> (TopT e) = TopT e

  WatchT ma <|> WatchT mb = WatchT $ HashMap.unionWith deepAlt ma mb
    where
      deepAlt :: (Trigger m -> m (TransactT m a))
              -> (Trigger m -> m (TransactT m a))
              -> (Trigger m -> m (TransactT m a))
      deepAlt fa fb s = (<|>) <$> fa s <*> fb s

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


instance (Applicative m) => Alternative (TransactT m) where
  empty = TT (\ _ -> empty)

  TT sa <|> TT sb = TT (\ s -> sa s <|> sb s)

instance (Monad m) => Monad (Transaction m) where
 TopT e >>= _ = TopT e
 BotT >>= _ = BotT
 WatchT ma >>= f = WatchT $ (map . map . map)
   (\ (TT sa) -> TT (\ s -> sa s >>= f )) ma

 LiftT a >>= f = LiftT $ (\ ta -> TT (\ s -> unTT ta s >>= f)) <$> a

 RunT a >>= f = LiftT . pure $ TT (\ s -> LiftT (pure <$> foldF (getMorph s) a) >>= f)

 ManyT a >>= f = ManyT . map (\ ta -> TT (\ s -> unTT ta s >>= f)) $  a

instance MonadTrans Transaction where
  lift = LiftT . map pure

instance (Monad m) => Monad (TransactT m) where
  TT sa >>= f = TT (\ s -> sa s >>= (\ x -> unTT (f x) s))

type KeyT m = Key (Transaction m)

deriving instance (Eq (Key m v)) => Eq (Key (Transaction m) v)
deriving instance (Hashable (Key m v)) => Hashable (Key (Transaction m) v)

instance ( MonadError e m
         , TransactionErr e
         , Typeable v
         , Typeable m
         , MonadLatMap v m)
  => MonadLatMap v (Transaction m) where

  newtype Key  (Transaction m) v = TrKey { unTrKey :: Key m v }
  type LatMemb (Transaction m) v = LatMemb m v
  type LatCons (Transaction m) v = LatCons m v

  -- | Actions to insert a value into the lattice are held w/in an F Edit
  --   so we can collect them and run them all at the end.
  putLat   :: (LatCons m v)
    => LatMemb m v
    -> Transaction m (KeyT m v)
  putLat l = map TrKey . RunT . liftF $ PutE l

  -- | Other actions (like getLat) tell us to wait on some term and when
  --   it changes run the action in the underlying monad.
  getLat :: (MonadLatMap v m, LatCons m v)
    => KeyT m v
    -> Transaction m (LatMemb m v)
  getLat (TrKey k) = WatchT . HashMap.singleton (TKey ktr k) $ \case
    TKey tr k' -> case eqTypeRep ktr tr of
      Nothing -> throwInvalidKeyType ktr tr
      Just HRefl -> pure <$> getLat k'
    t -> throwExpectedKeyTrigger t

    where

      ktr :: TypeRep v
      ktr = typeRep

  bindLat  :: (LatCons m v)
    => KeyT m v
    -> LatMemb m v
    -> Transaction m (KeyT m v)
  bindLat (TrKey k) l = map TrKey . RunT . liftF $ BindE k l

  equals   :: (LatCons m v)
    => KeyT m v
    -> KeyT m v
    -> Transaction m (KeyT m v)
  equals (TrKey a) (TrKey b) = map TrKey . RunT . liftF $ EqualsE a b

  subsumes :: (LatCons m v)
    => KeyT m v
    -> KeyT m v
    -> Transaction m Bool
  subsumes (TrKey a) (TrKey b) = RunT . liftF $ SubsumesE a b

instance (MonadTermGraph m) => MonadTermGraph (Transaction m) where

  type Term     t (Transaction m) = Term t m
  type Vert       (Transaction m) = Vert m
  type TermCons t (Transaction m) = TermCons t m

  addTerm :: (TermCons t m) => t (Vert m) -> Transaction m (Term t m)
  addTerm = RunT . liftF . AddE

  getTerm :: (TermCons t m) => Term t m -> Transaction m (t (Vert m))
  getTerm = lift . getTerm

instance ( MonadError e m
         , TransactionErr e
         , MonadPropRule v m
         , Typeable v
         , Typeable m) => MonadPropRule v (Transaction m) where

  getVert (TrKey k) = getVert k
  getKey v = lift $ TrKey <$> getKey @v @m v
