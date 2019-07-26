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


import qualified Control.Monad.Fail (fail)
import Control.Monad (ap)
import Data.IORef
import Control.Concurrent.Supply

newtype TermID t = TermID { getTermID :: Int }

newtype VarID m t = VarID { getVarID :: Int }

data Context = Context
  { _configData  :: Config
  , _assumptions :: Assumptions
  }

data Config = Config
  {
  }

data Assumptions = Assumptions
  {
  }

data TermSt

type TermMap = ()

type PropMap = ()

type RuleMap = ()

type RuleID = ()

type IntID = ()

data BindingState = BindingState
  { _termMap :: TermMap
  , _ruleMap :: RuleMap
  , _dependencies :: AdjacencyMap RuleState
  }

data TermState t
  = Forwarded { _target :: TermID t }
  | Bound { _boundState :: BoundState t }

data RuleState where
  Merged :: RuleID -> RuleState
  Watching :: forall m r. TypeRep m -> m [r ()] -> RuleState
  Updating :: forall m t. TypeRep m -> m (t (VarID m t)) -> RuleState

data BoundState t = BoundState
  { _termValue :: Maybe (t (TermID t))
  , _subsumed :: HashSet (TermID t)
  , _properties :: PropMap
  }
