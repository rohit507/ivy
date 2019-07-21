{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
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

import Ivy.Prelude hiding (IntSet, IntMap)
-- import Control.Lens hiding (Context)
-- import Control.Lens.TH

import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.Wrappers.IDs

import Ivy.Wrappers.IntMap (IntMap)
import qualified Ivy.Wrappers.IntMap as IM
import Ivy.Wrappers.IntSet (IntSet)
import qualified Ivy.Wrappers.IntSet as IS
import Ivy.Wrappers.IntGraph (IntGraph)
import qualified Ivy.Wrappers.IntGraph as IG
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.TypeMap.Dynamic.Alt (TypeMap, Item)
import qualified Data.TypeMap.Dynamic as TM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS

import Ivy.IntBindT

-- | Stuff that, for now we're just going to assume exists
instance () => Functor (Rule m)

instance () => Applicative (Rule m)

instance () => Monad (Rule m)

instance () => MonadFail (Rule m)

instance () => Alternative (Rule m)

ruleSet :: BoundStateIB t m -> RuleSet t m
ruleSet = undefined

modifyRuleSet :: (RuleSet t m -> RuleSet t m)
              -> BoundStateIB t m -> BoundStateIB t m
modifyRuleSet = undefined

type RuleTM t m = (
  Show (t (Var t (Rule m)))
  )

-- | Stuff to implement.

instance (MonadBind t m
         , RuleTM t m
         ) => MonadBind t (Rule m) where
  freeVar = undefined
  lookupVar = undefined
  bindVar = undefined

instance (MonadUnify t m
         , RuleTM t m
         ) => MonadUnify t (Rule m) where
  unify = undefined

instance (MonadSubsume t m
         , RuleTM t m
         ) => MonadSubsume t (Rule m) where
  subsume = undefined

instance (MonadProperty p t t' m
         , RuleTM t m
         , RuleTM t' m
         ) => MonadProperty p t t' (Rule m) where
   propertyOf = undefined

class MonadRule m where

  addRule :: (MonadBind t m) => Var t m -> (Var t m -> Rule m ()) -> m ()

instance MonadRule (IntBindT m) where

  addRule v r = undefined


data Rule m a where
  Lookup :: Var t m -> m (Rule m ()) -> Rule m ()
  Bind   :: Var t m -> m (t (Var t m)) -> Rule m ()
  Act    :: m a -> Rule m a

data RuleSet t m


addRuleT :: ()
         => VarIB t m -> (VarIB t m -> Rule (IntBindT m) ()) -> IBRWST m ()
addRuleT = undefined

runRuleT :: forall e m. (MonadError e m)
         => Rule (IntBindT m) () -> IBRWST m ()
runRuleT (Act m) = getIBT m
runRuleT (Lookup v m) = getIBT m >>= addRuleT v . const
runRuleT (Bind v mt) = undefined -- (getIBT mt >>= bindVarT @_ @_ @e v) *> skip

liftAddRule :: (MonadTransControl mt, MonadRule m)
            => (Var t (mt m) -> Rule (mt m) ()) -> mt m ()
liftAddRule = undefined

-- | Foo (\ a -> (b :+$ c) <- match a
--               guard $ b == c
--               set a (2 :*$ b))
--
--  add the handler to all potential terms
--    -- It'll match on !e = !d + !f
--    --   Will fail since !d != !f
--    -- Match on !g = !h + !h
--    --   Will pass guard, match on !g (again, and run its payload?)
--    --   Nah -- Is a problem
