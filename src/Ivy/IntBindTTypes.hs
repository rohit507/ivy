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

import Data.TypeMap.Dynamic (TypeMap, Item, OfType)
import qualified Data.TypeMap.Dynamic as TM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
-- import qualified Data.HashSet as HS
-- import qualified GHC.Base (Functor, fmap)
import Algebra.Graph.AdjacencyMap (AdjacencyMap)
import qualified Algebra.Graph.AdjacencyMap as G

-- import Data.Partition (Partition)
-- import qualified Data.Partition as P

-- import qualified Control.Monad.Fail (fail)
-- import Control.Monad (ap)
-- import Data.IORef
-- import Control.Concurrent.Supply


type BSM = RWST Context () BindingState

type BSEC e = (Typeable e)
type BSMC m = (Monad m, Typeable m)
type BSTC t = (Traversable t, Typeable t, Eq1 t, Functor t)
type BSMTC m t = (BSMC m, BSTC t, Newtype (Var (IntBindT m) t) Int)
type BSEMC e m = (MonadError e m, BSMC m, BSEC e)
type BSETC e t = (BSEC e, BSTC t, JoinSemiLattice1 e t)
type BSEMTC e m t = (BSETC e t, BSMTC m t, BSEMC e m)


type UnivID = Int


instance Newtype Int Int where
  pack = id
  unpack = id

newtype TermID (t :: Type -> Type) = TermID { getTermID :: Int }
  deriving newtype (Eq, Ord, Show, Hashable, NFData)

deriving instance Generic (TermID t)

instance Newtype (TermID t) Int where
  pack = TermID
  unpack = getTermID

newtype VarID m t = VarID { getVarID :: Int }
  deriving newtype (Eq, Ord, Show, Hashable, NFData)

deriving instance Generic (VarID m t)

instance Newtype (VarID m t) Int where
  pack = VarID
  unpack = getVarID

newtype RuleID = RuleID { getRuleID :: Int }
  deriving newtype (Eq, Ord, Show, Hashable, NFData)

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
  , _assumptions :: Assertions UnivID
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

instance Typeable t => At (TermMap t) where
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
              TM.insert (typeRep @(Term t)) (HM.update (const mts) tid mt) x
            Nothing ->
              TM.insert (typeRep @(Term t)) (HM.update (const mts) tid mempty) x

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
  , _assertions    :: Assertions UnivID
  }

initialBindingState :: Supply -> BindingState
initialBindingState s = BindingState s mempty emptyTMap mempty G.empty mempty TM.empty mempty

data TermState t where

  Forwarded :: { _target :: TermID t } -> TermState t
  Bound :: { _boundState :: BoundState t } -> TermState t

freeBoundState :: BoundState t
freeBoundState = BoundState Nothing TM.empty

freeTermState :: TermState t
freeTermState = Bound freeBoundState


data PropRel where
  PropRel :: forall e p t t'. (BSETC e t, BSETC e t', Property p t t')
    => TypeRep e -> TypeRep p -> TypeRep t -> TypeRep t' -> TermID t' -> PropRel

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

runIntBindT :: Config -> Supply -> IntBindT m a -> m (a, BindingState, ())
runIntBindT c s = (\ m -> runRWST m (initialContext c) (initialBindingState s)) . getIntBindT

data RuleHistories = RuleHistories
  { _term :: Maybe RuleID
  , _nextStep :: HashMap ExID RuleHistories }
  deriving (Eq, Ord)

data RuleHistory = RuleHistory
  { _family :: RuleID
  , _nextStep :: [ExID] }
  deriving (Eq, Ord)

data RuleMeta = RuleMeta
                { _history    :: RuleHistory
  , _watched    :: HashSet ExID
  , _assumptions :: Assertions UnivID
  }

newRuleMeta :: RuleID -> RuleMeta
newRuleMeta rid = RuleMeta (RuleHistory rid []) mempty mempty

type RT = StateT RuleMeta
type RTIB m = RT (IntBindT m)
type RuleIB m = Rule (IntBindT m)

-- | Rules let us describe invariants over a term map as actions that
--   can be run repeatedly/incrementally executed. In general they only
--   really hook into lookups and bind in order to correctly capture
--   dependencies where it matters.
--
--   Despite the T suffix this isn't actually (yet) a monad transformer.
--   It mostly exists to
--
--   FIXME :: This looks suspiciously like some conbination of a
--            continuation monad and a free monad. See if there's
--            someway to refactor into those.
data RuleT m a where
  RLook :: (MonadBind e m t, Eq1 t)
    => { _type :: TypeRep t
       , _var :: Var m t
       , _process :: Maybe (t (Var m t)) -> RT m (RuleT m a)
       } -> RuleT m a

  RLift :: ()
    => { _action :: RT m [RuleT m a] } -> RuleT m a

  RPure :: ()
    => { _actions :: a
       } -> RuleT m a

rtLift :: (Monad m, Applicative (RuleT m)) => RT m a -> RuleT m a
rtLift m = RLift $ m >>= pure . pure . pure

rtDrop :: (Monad m, Applicative (RuleT m)) => RuleT m a -> RT m [RuleT m a]
rtDrop = pure . pure

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
