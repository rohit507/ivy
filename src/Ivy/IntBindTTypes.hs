{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.IntBindTTypes where

import Intro hiding (Item)
import Ivy.Prelude
-- import Control.Lens hiding (Context)
-- import Control.Lens.TH

import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.Assertions

import qualified Text.Show as S
import Data.TypeMap.Dynamic (TypeMap, Item, OfType)
import qualified Data.TypeMap.Dynamic as TM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
-- import qualified Data.HashSet as HS
-- import qualified GHC.Base (Functor, fmap)
-- import qualified GHC.Base (fmap)
-- import Algebra.Graph.AdjacencyMap (AdjacencyMap)
import Algebra.Graph.AdjacencyMap (AdjacencyMap)
import qualified Algebra.Graph.AdjacencyMap as G


-- import Data.Partition (Partition)
-- import qualified Data.Partition as P

import qualified Control.Monad.Fail as F (fail)
-- import Control.Monad (ap)
-- import Data.IORef
-- import Control.Concurrent.Supply


type BSM = RWST Context () BindingState

type BSEC e = (Typeable e, Show e)
type BSMC m = (Monad m, Typeable m, GetErr m, Show (Err m))

type BSTC t = (Traversable t, Typeable t, Eq1 t, Functor t)

type BSMTC m t = (BSMC m, BSTC t
                 , Newtype (Var (IntBindT m) t) Int
                 )

type BSEMC e m = (MonadError e m, BSMC m, BSEC e, Err m ~ e)

type BSETC e t = (BSEC e, BSTC t, JoinSemiLattice1 e t)

type BSEMTC e m t = (BSETC e t, BSMTC m t, BSEMC e m)

type UnivID = Int

instance Newtype Int Int where
  pack = id
  unpack = id

newtype TermID (t :: Type -> Type) = TermID { getTermID :: Int }
  deriving newtype (Eq, Ord, Hashable, NFData)

deriving instance Show (TermID t)
deriving instance Generic (TermID t)

instance Newtype (TermID t) Int where
  pack = TermID
  unpack = getTermID

newtype VarID m t = VarID { getVarID :: Int }
  deriving newtype (Eq, Ord, Hashable, NFData)

deriving instance Show (VarID m t)
deriving instance Generic (VarID m t)

instance Newtype (VarID m t) Int where
  pack = VarID
  unpack = getVarID

newtype RuleID = RuleID { getRuleID :: Int }
  deriving newtype (Eq, Ord, Hashable, NFData)

deriving instance Show RuleID
deriving instance Generic RuleID

instance Newtype RuleID Int where
  pack = RuleID
  unpack = getRuleID

forceTID :: VarID m t -> TermID t
forceTID = force

forceVID :: forall m t. TermID t -> VarID m t
forceVID = force

data ExID where
  TID :: (BSTC t) => TypeRep t -> TermID t -> ExID
  RID :: () => RuleID -> ExID

instance Show ExID where
  show = showExID

showExID :: ExID -> String
showExID (TID _tt t) = "(TID " {- (typeRep @(" <> show tt <> ")) ("-} <> show t <> "))"
showExID (RID r) = "(RID (" <> show r <> "))"

instance Eq ExID where
  (RID r) == (RID r') = r == r'
  (TID tr t) == (TID tr' t') = fromMaybe False $ do
    HRefl <- eqTypeRep tr tr'
    pure $ t == t'
  _ == _ = False

instance Ord ExID where
  compare (RID _) (TID _ _) = LT
  compare (TID _ _) (RID _) = GT
  compare (RID r) (RID r')  = compare r r'
  compare (TID _ t) (TID _ t') = compare (unpack t) (unpack t')

instance Hashable ExID where
  hashWithSalt s (RID r) = hashWithSalt s r
  hashWithSalt s (TID _ t) = hashWithSalt s t

class ToExID a where
  toExID :: a -> ExID

instance ToExID RuleID where
  toExID = RID

instance (BSTC t) => ToExID (TermID t) where
  toExID = TID typeRep


data Context = Context
  { _config  :: Config
  -- | Things we assume are true
  , _assumptions :: Assertions SomeVar
  }

data Config = Config
  {
  }


initialContext :: Config -> Context
initialContext c = Context c mempty


data Term t
newtype TMap = TMap { getTMap :: forall t. Typeable t => TermMap t }

emptyTMap :: TMap
emptyTMap = TMap $ TermMap TM.empty

type instance Item TMap (Term t) = HashMap (TermID t) (TermState t)

newtype TermMap (t :: Type -> Type) = TermMap { getTermMap :: TypeMap TMap }

forceTermMap :: TermMap t -> (forall s. (Typeable s) => TermMap s)
forceTermMap (TermMap x) = TermMap x

forceTMap :: TermMap t -> TMap
forceTMap (TermMap x) = TMap (TermMap x)

type instance Index (TermMap t) = TermID t
type instance IxValue (TermMap t) = TermState t

instance (Typeable t) => Ixed (TermMap t)

instance (Typeable t) => At (TermMap t) where
  at :: TermID t -> Lens' (TermMap t) (Maybe (TermState t))
  at tid = lens getter (flip fsetter)
    where
      getter :: TermMap t -> Maybe (TermState t)
      getter (TermMap x) = do
         res <- TM.lookup (typeRep @(Term t)) x
         HM.lookup tid res

      fsetter :: Maybe (TermState t)
              -> TermMap t -> TermMap t
      fsetter mts (TermMap x)
        = TermMap $ case TM.lookup (typeRep @(Term t)) x of
            Just mt ->
              TM.insert (typeRep @(Term t)) (HM.alter (const mts) tid mt) x
            Nothing ->
              TM.insert (typeRep @(Term t)) (HM.alter (const mts) tid mempty) x

data DefaultRule (t :: Type -> Type) where
  DefaultRule :: (MonadRule e m, MonadBind e m t)
              => TypeRep e
              -> TypeRep m
              -> [Var m t -> Rule m ()]
              -> DefaultRule t

data RMap
type instance Item RMap (Term t) = DefaultRule t

type RuleMap = TypeMap RMap

data BindingState = BindingState
  { _supply        :: Supply
  , _idents        :: HashMap UnivID ExID
  , _terms_        :: TMap
  , _rules         :: HashMap RuleID RuleState
  , _dependencies  :: AdjacencyMap ExID
  , _ruleHistories :: HashMap RuleID RuleHistories
  , _defaultRules  :: RuleMap
  , _assertions    :: Assertions SomeVar
  , _dirtySet      :: HashSet ExID
  }

initialBindingState :: Supply -> BindingState
initialBindingState s = BindingState
  { _supply        = s
  , _idents        = mempty
  , _terms_        = emptyTMap
  , _rules         = mempty
  , _dependencies  = G.empty
  , _ruleHistories = mempty
  , _defaultRules  = TM.empty
  , _assertions    = mempty
  , _dirtySet      = mempty
  }

data TermState t where

  Forwarded :: { _target :: TermID t } -> TermState t
  Bound :: { _boundState :: BoundState t } -> TermState t

deriving instance Show (t (TermID t)) => Show (BoundState t)
deriving instance Show (t (TermID t)) => Show (TermState t)

freeBoundState :: BoundState t
freeBoundState = BoundState Nothing TM.empty

freeTermState :: TermState t
freeTermState = Bound freeBoundState

data PropRel where
  PropRel :: forall e p. (BSETC e (From p), BSETC e (To p), Property p)
    => TypeRep e -> TypeRep p -> TermID (To p) -> PropRel

deriving instance Show PropRel

type PropMap = TypeMap (OfType PropRel)

data BoundState t = BoundState
  { _termValue :: Maybe (t (TermID t))
  , _properties :: PropMap
  }

data RuleState where
  Merged :: RuleID -> RuleState
  Waiting :: (Typeable m)
    => TypeRep m -> RuleMeta -> Rule m () -> RuleState


newtype IntBindT m a = IntBindT { getIntBindT :: BSM m a }

instance (GetErr m) => GetErr (IntBindT m) where
  type Err (IntBindT m) = Err m

runIntBindT :: Config -> Supply -> IntBindT m a -> m (a, BindingState, ())
runIntBindT c s = (\ m -> runRWST m (initialContext c) (initialBindingState s)) . getIntBindT

instance MFunctor IntBindT where
  hoist f (IntBindT m) = IntBindT $ hoist f m

data RuleHistories = RuleHistories
  { _term :: Maybe RuleID
  , _nextStep :: HashMap ExID (HashMap Int RuleHistories) }
  deriving (Eq, Ord, Show)

data RuleHistory = RuleHistory
  { _family :: RuleID
  , _nextStep :: [(ExID,Int)] }
  deriving (Eq, Ord, Show)

type SomeVarC m t =  (Ord (Var m t)
                     , Typeable m
                     , Typeable t
                     , Hashable (Var m t)
                     , Show (Var m t))

data SomeVar where
  SomeVar :: SomeVarC m t
    => TypeRep m -> TypeRep t -> Var m t -> SomeVar

instance Show SomeVar where
  show (SomeVar m t v) = "(SomeVar (typeRep @(" <> show m <> ")) (typeRep @("
     <> show t <> ")) ("<> show v <> "))"

instance Eq SomeVar where
  (SomeVar m t v) == (SomeVar m' t' v')
    = fromMaybe False $ do
       HRefl <- eqTypeRep m m'
       HRefl <- eqTypeRep t t'
       pure $ v == v'


instance Ord SomeVar where
  compare (SomeVar m t v) (SomeVar m' t' v')
    = case compare (someTypeRep m) (someTypeRep m') of
       EQ -> case compare (someTypeRep t) (someTypeRep t') of
         EQ -> fromMaybe (panic "unreachable") $ do
           HRefl <- eqTypeRep m m'
           HRefl <- eqTypeRep t t'
           pure $ compare v v'
         a -> a
       a -> a

instance Hashable SomeVar where
  hashWithSalt s (SomeVar _ _ v) = hashWithSalt (s + 1) v

data RuleMeta = RuleMeta
  { _history    :: RuleHistory
  , _watched    :: HashSet ExID
  , _assumptions :: Assertions SomeVar
  }

deriving instance Show RuleMeta

fromSomeVar :: forall m t. (Typeable m, Typeable t) => SomeVar -> Maybe (Var m t)
fromSomeVar (SomeVar tm tt v) = do
  HRefl <- eqTypeRep tm (typeRep @m)
  HRefl <- eqTypeRep tt (typeRep @t)
  pure v

toSomeVar :: forall m t. (SomeVarC m t) => Var m t -> SomeVar
toSomeVar v = SomeVar (typeRep @m) (typeRep @t) v

newRuleMeta :: RuleID -> RuleMeta
newRuleMeta rid = RuleMeta (RuleHistory rid []) mempty mempty

data LookF a where
  Lookup :: (MonadBind (Err m) m t)
    => TypeRep m -> TypeRep t -> Var m t -> LookF (Maybe (t (Var m t)))

type RT m = ExceptT (Err m) (StateT RuleMeta (LogicT m))
type RTP m = ProgramT LookF (RT m)

newtype RuleT m a where
  RuleT :: {getRuleT :: RTP m a} -> RuleT m a

type RTIB m = RT (IntBindT m)
type RuleIB m = Rule (IntBindT m)

deriving newtype instance (Monad m) => Functor (RuleT m)
deriving newtype instance (Monad m) => Applicative (RuleT m)
deriving newtype instance (Monad m) => Monad (RuleT m)

deriving newtype instance (MonadError e m, GetErr m, Err m ~ e) => MonadError e (RuleT m)

instance (Monad m) => Alternative (RuleT m) where
  empty = RuleT . lift . lift . lift $ (empty :: LogicT m a)
  (RuleT a) <|> (RuleT b) = RuleT . join . lift $ alternated >>= \case
    Return a -> pure . pure $ a
    inst :>>= f -> pure $ singleton inst >>= f

    where

      alternated = ExceptT $ StateT $ \ s -> do
        interleave (flip runStateT s . runExceptT $ viewT a)
                   (flip runStateT s . runExceptT $ viewT b)

instance (Monad m) => MonadPlus (RuleT m)

instance (Monad m) => MonadFail (RuleT m) where
  fail s = if
    | "Pattern match failure" `isPrefixOf` s ->
            RuleT . lift . lift . lift $ F.fail s
    | otherwise -> panic $ convertString s

instance (GetErr m) => GetErr (RuleT m) where
  type Err (RuleT m) = Err m

instance MonadTrans RuleT where
  lift = RuleT . liftRTP

liftRT :: (Monad m) => m a -> RT m a
liftRT = lift . lift . lift

liftRTP :: (Monad m) => m a -> RTP m a
liftRTP = lift . liftRT

execRule :: forall m a. (Monad m, Typeable m)
         => (forall t. (MonadBind (Err m) m t) => Var m t -> RT m ())
         -> (forall t. (MonadBind (Err m) m t) => Var m t -> RT m (Maybe (t (Var m t))))
         -> RuleT m a -> RT m (Either a (RuleT m a))
execRule note lookup act = (viewT . getRuleT $ act) >>= \case
  Return a -> pure $ Left a
  (Lookup tm __ v) :>>= f -> fromMaybe (panic "unreachable") $ do
      HRefl <- eqTypeRep tm (typeRep @m)
      pure $ do
        note v
        pure . Right . RuleT $ (lift $ lookup v) >>= f

makeFieldsNoPrefix ''Context
makeFieldsNoPrefix ''Config
makeFieldsNoPrefix ''BindingState
makeFieldsNoPrefix ''RuleState
makeFieldsNoPrefix ''RuleHistory
makeFieldsNoPrefix ''RuleHistories
makeFieldsNoPrefix ''BoundState
makeFieldsNoPrefix ''RuleMeta
-- makePrisms ''RuleState

class HasTerms s a where
  terms :: Lens' s a

instance (Typeable a) => HasTerms BindingState (TermMap a) where
  terms = (terms_ :: Lens' BindingState TMap)
        . (iso getTMap forceTMap)

instance HasAssertions (Assertions a) (Assertions a) where
  assertions = id

instance Monoid w => MonadTransControl (RWST r w s) where
   type StT (RWST r w s) a = (a, s, w)
   liftWith f =
       rwsT $ \r s -> map (\x -> (x, s, mempty :: w))
                                   (f $ \t -> runRWST t r s)
   restoreT mSt = rwsT $ \_ _ -> mSt
   {-# INLINABLE liftWith #-}
   {-# INLINABLE restoreT #-}
