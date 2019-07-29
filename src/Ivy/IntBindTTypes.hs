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


type RuleMap = HashMap RuleID RuleState
type PropMap = () -- HashMap RuleID RuleState

data BindingState = BindingState
  { _find         :: HashMap UnivID ExID
  , _terms_       :: TMap
  , _rules        :: RuleMap
  , _dependencies :: AdjacencyMap UnivID
  }


data TermState t where

  Forwarded :: { _target :: TermID t } -> TermState t
  Bound :: { _boundState :: BoundState t } -> TermState t

data RuleState where
  Merged :: RuleID -> RuleState
  Watching :: forall m r. TypeRep m -> m [r ()] -> RuleState
  Updating :: forall m t. TypeRep m -> m (t (VarID m t)) -> RuleState

data BoundState t = BoundState
  { _termValue :: Maybe (t (TermID t))
  , _subsumed :: HashSet (TermID t)
  , _properties :: PropMap
  }

makeFieldsNoPrefix ''Context
makeFieldsNoPrefix ''Config
makeFieldsNoPrefix ''Assumptions
makeFieldsNoPrefix ''BindingState
makeFieldsNoPrefix ''RuleState
makeFieldsNoPrefix ''BoundState
makePrisms ''RuleState

terms :: (Typeable t, Typeable s)
      => Lens BindingState BindingState (TermMap t) (TermMap s)
terms = (terms_ :: Lens' BindingState TMap)
      . (iso getTMap forceTMap)
