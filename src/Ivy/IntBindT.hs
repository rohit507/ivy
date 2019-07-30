
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

module Ivy.IntBindT where

import Ivy.Prelude hiding (IntSet, IntMap)
-- import Control.Lens hiding (Context)
-- import Control.Lens.TH

import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.IntBindTTypes


import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
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

-- instance Functor (IntBindT m)
-- instance Applicative (IntBindT m)
-- instance Monad (IntBindT m)
-- instance MonadError e (IntBindT m)

instance MonadTrans IntBindT where
  lift = undefined

instance MonadTransConstrol IntBindT where
  liftWith = undefined
  restoreT = undefined

type VarIB m = VarID (IntBindT m)

instance ( Typeable t
         , Traversable t
         , Monad m
         , MonadError e m)
         => MonadBind e t (IntBindT m) | m -> e where

  type Var (IntBindT m) = VarID (IntBindT m)

  freeVar :: IntBindT m (VarIB m t)
  freeVar = undefined

  lookupVar :: VarIB m t -> IntBindT m (Maybe (t (VarIB m t)))
  lookupVar = undefined

  bindVar :: VarIB m t -> t (VarIB m t) -> IntBindT m (VarIB m t)
  bindVar = undefined

  redirectVar :: VarIB m t -> VarIB m t -> IntBindT m (VarIB m t)
  redirectVar = undefined

type BSM = StateT BindingState

freeVarS :: BSM m (TermID t)
freeVarS = undefined

lookupVarS :: TermID t -> BSM m (Maybe (t (TermID t)))
lookupVarS = undefined

bindVarS :: TermID t -> t (TermID t) -> BSM m (TermID t)
bindVarS = undefined

redirectVarS :: TermID t -> TermID t -> BSM m (TermID t)
redirectVarS = undefined

propertyOfS :: (Property p t t') => p -> TermID t -> BSM m (TermID t')
propertyOfS = undefined

getPropertyPairsS :: forall a t. ()
    => (forall t' p. () => p -> These (TermID t') (TermID t') -> BSM m a)
    -> (BSM m a -> BSM m a -> BSM m a)
    -> a
    -> TermID t -> TermID t -> BSM m a
getPropertyPairsS = undefined

type RAM = ReaderT Assumptions

isAssumedEqualR :: TermID t -> TermID t -> RAM m Bool
isAssumedEqualR = undefined

assumeEqualR :: TermID t -> TermID t -> RAM m a -> RAM m a
assumeEqualR = undefined

isAssumedUnifiedR :: TermID t -> TermID t -> Ram m Bool
isAssumedUnifiedR = undefined

assumeUnifiedR :: TermID t -> TermID t -> RAM m a -> RAM m a
assumeUnifiedR = undefined

isAssumedSubsumedR :: TermID t -> TermID t -> RAM m Bool
isAssumedSubsumedR = undefined

assumeSubsumedR :: TermID t -> TermID t -> RAM m Bool
assumeSubsumedR = undefined

-- instance MonadProperty e p (IntBindT m) where
-- instance MonadProperties e (IntBindT m) where

-- instance Functor (AssumeT m)
-- instance Applicative (AssumeT m)
-- instance Monad (AssumeT m)
-- instance MonadError e (AssumeT m)
-- instance MonadBind e t (AssumeT m) where
-- instance MonadProperty e p (AssumeT t M) where
-- instance MonadProperties e (AssumeT m) where
-- instance MonadAssume e t (AssumeT m) where
-- instance MonadUnify e t (AssumeT m) where

-- instance Functor (Rule m)
-- instance Applicative (Rule m)
-- instance Monad (Rule m)
-- instance MonadError e (Rule m)
-- instance MonadBind e t (Rule m) where
-- instance MonadProperty e p (Rule m) where
-- instance MonadProperties e (Rule m) where
-- instance MonadAssume e t (AssumeT (RuleT m)) where
-- instance MonadUnify e t (AssumeT (RuleT m))

-- This instance is weird, in that we need to be aware of both the parent and
-- child assumptions, and clearly differentiate between them.
-- instance MonadRule e (AssumeT (Rule (AssumeT (IntBindT m)))) AssumeT (IntBindT m) where


instance MonadTrans AssumeT where
  lift = undefined

instance MonadTransConstrol AssumeT where
  liftWith = undefined
  restoreT = undefined

instance Functor (Rule m) where
  fmap = undefined

instance Applicative (Rule m) where
  pure = undefined
