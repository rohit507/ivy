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

import Ivy.Prelude hiding (IntSet, IntMap)
-- import Control.Lens hiding (Context)
-- import Control.Lens.TH

import Algebra.Lattice
import Ivy.MonadClasses

import Data.TypeMap.Dynamic (TypeMap, Item, OfType)
import qualified Data.TypeMap.Dynamic as TM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import qualified GHC.Base (Functor, fmap)
import Algebra.Graph.AdjacencyMap (AdjacencyMap)
import qualified Algebra.Graph.AdjacencyMap as G

import Data.Partition (Partition)
import qualified Data.Partition as P

import qualified Control.Monad.Fail (fail)
import Control.Monad (ap)
import Data.IORef
import Control.Concurrent.Supply


newtype UnivID = UnivID { getUnivID :: Int }
  deriving newtype (Eq, Ord, Show, Hashable, NFData)

deriving instance Generic UnivID

instance Newtype UnivID Int where
  pack = UnivID
  unpack = getUnivID

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

force :: forall b a c. (Newtype a c, Newtype b c) => a -> b
force = pack . unpack

data ExID where
  VID :: () => TypeRep m -> TypeRep t -> VarID m t -> ExID
  RID :: () => RuleID -> ExID
  -- deriving (Eq, Ord, Show, Generic, Hashable, NFData)

data Context = Context
  { _config  :: Config
  , _assumptions :: Assumptions
  }

data Config = Config
  {
  }

data Assumptions = Assumptions
  { _equalities   :: Partition UnivID
  , _unifications :: Partition UnivID
  , _subsumptions :: HashMap UnivID (HashSet UnivID)
  }

data Term t
newtype TMap = TMap { getTMap :: forall t. Typeable t => TermMap t }

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

data BindingState = BindingState
  { _supply        :: Supply
  , _idents        :: HashMap UnivID ExID
  , _terms_        :: TMap
  , _rules         :: HashMap RuleID RuleState
  , _dependencies  :: AdjacencyMap ExID
  , _ruleHistories :: HashMap RuleID RuleHistory
  }

data TermState t where

  Forwarded :: { _target :: TermID t } -> TermState t
  Bound :: { _boundState :: BoundState t } -> TermState t


type PropMap = ()
data BoundState t = BoundState
  { _termValue :: Maybe (t (TermID t))
  , _subsumed :: HashSet (TermID t)
  , _properties :: PropMap
  }

data RuleState where
  -- | Rule has been collapsed into another rule
  Merged :: RuleID -> RuleState
  -- | Rule that can modify m or generate new rules as is reasonable.
  Held :: forall m. ()
           => TypeRep m
           -> m [Rule m ()]
           -> RuleState

data RuleHistory = RuleHistory
  { _nextStep :: HashMap (RuleAction, UnivID) RuleHistory }
  deriving (Eq, Ord, Show)


data RuleAction = Lookup | Bind
  deriving (Eq, Ord, Show)

-- | The Rule Monad which we use to perform
data Rule m a where
  LookupVar :: (Typeable t)
         => TypeRep t
         -> VarID m t
         -> (Maybe (t (Var m t)) -> m [Rule m a])
         -> Rule m a

  BindVar :: (Typeable t)
       => TypeRep t
       -> VarID m t
       -> m (t (VarID m t))
       -> m [Rule m a]
       -> Rule m a

  Pure :: a -> Rule m a

  Act :: m a -> Rule m a

  Fin :: Rule m a

newtype AssumeT m a = AssumeT { getAssumeT :: ReaderT Assumptions m a }

newtype IntBindT m a = BindT { getIntBindT :: StateT BindingState m a }

makeFieldsNoPrefix ''Context
makeFieldsNoPrefix ''Config
makeFieldsNoPrefix ''Assumptions
makeFieldsNoPrefix ''BindingState
makeFieldsNoPrefix ''RuleState
makeFieldsNoPrefix ''BoundState
makePrisms ''RuleState

class HasTerms s a where
  terms :: Lens' s a

instance (Typeable a) => HasTerms BindingState (TermMap a) where
  terms = (terms_ :: Lens' BindingState TMap)
        . (iso getTMap forceTMap)
