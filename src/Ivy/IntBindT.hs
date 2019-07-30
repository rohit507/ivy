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

newtype IntBindT m a = IntBindT { getIntBindT :: StateT BindingState m a }

deriving newtype instance (Functor m) => Functor (IntBindT m)
deriving newtype instance (Monad m) => Applicative (IntBindT m)
deriving newtype instance (Monad m) => Monad (IntBindT m)
deriving newtype instance (MonadError e m) => MonadError e (IntBindT m)

instance MonadTrans IntBindT where
  lift = IntBindT . lift

instance MonadTransControl IntBindT where

  type StT IntBindT a = StT (StateT BindingState) a

  liftWith = defaultLiftWith IntBindT getIntBindT
  restoreT = defaultRestoreT IntBindT

type VarIB m = VarID (IntBindT m)

instance (BSEMTC e m t, Eq1 t)
         => MonadBind e t (IntBindT m) where

  type Var (IntBindT m) = VarID (IntBindT m)

  freeVar :: IntBindT m (VarIB m t)
  freeVar = IntBindT $ force @(VarIB m t) <$> freeVarS

  lookupVar :: VarIB m t -> IntBindT m (Maybe (t (VarIB m t)))
  lookupVar
    = IntBindT
    . map (map . map $ force @(VarIB m t))
    . lookupVarS @m @t
    . force @(TermID t)

  bindVar :: VarIB m t -> t (VarIB m t) -> IntBindT m (VarIB m t)
  bindVar v t = IntBindT $ force <$> (bindVarS (force v) $ map force t)

  redirectVar :: VarIB m t -> VarIB m t -> IntBindT m (VarIB m t)
  redirectVar a b = IntBindT $ force <$> redirectVarS (force a) (force b)


freeVarS :: forall m t. (BSMTC m t) =>  BSM m (TermID t)
freeVarS = do
  nv :: TermID t <- newIdent
  setTermState nv freeTermState
  addTermToDeps nv
  addTermToIdents nv
  runDefaultRules nv
  pure nv

lookupVarS :: forall m t. (BSMTC m t) => TermID t -> BSM m (Maybe (t (TermID t)))
lookupVarS t = getTermState t >>= \case
  Forwarded _ -> panic "Unreachable: getRepresentative always returns bound term."
  Bound bs  -> traverse freshenTerm (bs ^. termValue)

bindVarS :: forall m t. (BSMTC m t) => TermID t -> t (TermID t) -> BSM m (TermID t)
bindVarS v t = do
  mot <- lookupVarS v
  nt  <- freshenTerm t
  whenJust mot $ \ ot -> do
    let otd = foldMap (HS.singleton . toExID) ot
        ntd = foldMap (HS.singleton . toExID) nt
        tv = toExID v
        lostDeps = HS.difference otd ntd
        newDeps  = HS.difference ntd otd
    unless (HS.null lostDeps) $
      traverse_ (tv `doesNotDependOn`) $ HS.toList lostDeps
    unless (HS.null newDeps) $
      traverse_ (tv `dependsOn`) $ HS.toList newDeps
  setTermValue v $ Just nt
  -- When the term has changed in some salient way we need to push updates.
  when (fromMaybe True $ (liftEq (==)) <$> (Just nt) <*> mot)
    $ pushUpdates (toExID v)
  getRepresentative v

redirectVarS :: forall m t. (BSMTC m t) => TermID t -> TermID t -> BSM m (TermID t)
redirectVarS old new = do
  o' <- getRepresentative old
  n' <- getRepresentative new
  when (o' /= n') $ do
    let to' = toExID o'
        tn' = toExID n'
    -- Move depends from old to new
    getDependencies to' >>= traverse_ (manageDependencies to' tn')
    getDependents   tn' >>= traverse_ (manageDependents   to' tn')
    to' `dependsOn` tn'
    lookupVarS o' >>= setTermValue n'
    setTermState o' $ Forwarded n'
    dirty  <- (||) <$> redirectRelations o' n' <*> redirectRules o' n'
    when dirty $ pushUpdates tn'
  getRepresentative n'

  where

    manageDependencies old new dep = do
      dep `doesNotDependOn` old
      dep `dependsOn`       new

    manageDependents old new dep = do
      old `doesNotDependOn` dep
      new `dependsOn`       dep

instance (forall t. (BSETC e t) => (BSEMTC e m t), BSEMC e m, Typeable p)
         => MonadProperty e p (IntBindT m) where

  propertyOf :: (BSEMTC e m t, BSEMTC e m t', Property p t t')
      => p -> VarIB m t -> IntBindT m (VarIB m t')
  propertyOf p var = IntBindT $ force <$> propertyOfS p (force var)

propertyOfS :: forall p m t t'. (Property p t t', BSMTC m t, BSMTC m t')
            => p -> TermID t -> BSM m (TermID t')
propertyOfS p v = getProperty p v >>= \case
  Nothing -> do
    r :: TermID t' <- freeVarS
    setProperty p v r
    pure r
  Just r -> pure r

instance (forall t. (BSETC e t) => (BSEMTC e m t)) => MonadProperties e (IntBindT m) where

  getPropertyPairs :: forall a t. (BSEMTC e m t)
      => (forall t' p proxy. (BSEMTC e m t' , Property p t t', MonadProperty e p (IntBindT m))
                      => proxy p -> These (VarIB m t') (VarIB m t') -> IntBindT m a)
      -> (a -> a -> IntBindT m a)
      -> a
      -> VarIB m t -> VarIB m t -> IntBindT m a
  getPropertyPairs f mappendM mempty a b
    = IntBindT $ getPropertyPairsS f' mappendM' mempty (force a) (force b)

    where

      f' :: forall t' p proxy. (BSEMTC e m t', BSEMTC e m t, Property p t t', MonadProperty e p (IntBindT m))
         => proxy p -> These (TermID t') (TermID t') -> BSM m a
      f' p t = getIntBindT $ (f p (bimap force force t) :: IntBindT m a)

      mappendM' :: a -> a -> BSM m a
      mappendM' a b = getIntBindT $ mappendM a b

getPropertyPairsS :: forall a e m t. (BSEMTC e m t)
    => (forall t' p proxy. (BSEMTC e m t', Property p t t', MonadProperty e p (IntBindT m))
              => proxy p -> These (TermID t') (TermID t') -> BSM m a)
    -> (a -> a -> BSM m a)
    -> a
    -> TermID t -> TermID t -> BSM m a
getPropertyPairsS f mappend mempty a b = do
  pma <- getPropMap a
  pmb <- getPropMap b
  let theseMap :: TypeMap (OfType ())
        = TM.intersection (TM.map empty pma) pmb
      thisMap :: TypeMap (OfType ())
        = TM.difference (TM.map empty pma) theseMap
      thatMap :: TypeMap (OfType ())
        = TM.difference (TM.map empty pmb) theseMap
  these :: [a] <- catMaybes . TM.toList
    <$> TM.traverse (theseOp pma pmb) theseMap
  that :: [a] <- catMaybes . TM.toList <$> TM.traverse (thatOp pma) thatMap
  this :: [a] <- catMaybes . TM.toList <$> TM.traverse (thisOp pma) thisMap
  foldrM mappend mempty $ this <> that <> these

  where

    empty :: forall t a. (Typeable t)
       => Proxy t -> a -> ()
    empty _ _ = ()

    theseOp :: forall p proxy. (Typeable p)
          => PropMap
          -> PropMap
          -> proxy p
          -> ()
          -> BSM m (Maybe a)
    theseOp rma rmb p _ = sequenceA $ do
      (PropRel te  tp  to  t  v ) <- TM.lookup (typeRep @p) rma
      (PropRel te' tp' to' t' v') <- TM.lookup (typeRep @p) rmb
      HRefl <- eqTypeRep t t'
      HRefl <- eqTypeRep tp tp'
      HRefl <- eqTypeRep tp (typeRep @p)
      HRefl <- eqTypeRep te te'
      HRefl <- eqTypeRep te (typeRep @e)
      HRefl <- eqTypeRep to to'
      HRefl <- eqTypeRep to (typeRep @t)
      pure $ f p (These v v')

    thisOp :: forall p proxy. (Typeable p)
          => PropMap
          -> proxy p
          -> ()
          -> BSM m (Maybe a)
    thisOp rma p _ = sequenceA $ do
      (PropRel te  tp  to  t  v ) <- TM.lookup (typeRep @p) rma
      HRefl <- eqTypeRep tp (typeRep @p)
      HRefl <- eqTypeRep te (typeRep @e)
      HRefl <- eqTypeRep to (typeRep @t)
      pure $ f p (This v)

    thatOp :: forall p proxy. (Typeable p)
          => PropMap
          -> proxy p
          -> ()
          -> BSM m (Maybe a)
    thatOp rmb p _ = sequenceA $ do
      (PropRel te  tp  to  t  v ) <- TM.lookup (typeRep @p) rmb
      HRefl <- eqTypeRep tp (typeRep @p)
      HRefl <- eqTypeRep te (typeRep @e)
      HRefl <- eqTypeRep to (typeRep @t)
      pure $ f p (That v)


newIdent :: forall o m s. (MonadState s m, HasSupply s Supply, Newtype o Int)
         => m o
newIdent = map pack $ supply %%= freshId

setTermState :: forall m t. (BSMTC m t) => TermID t -> TermState t ->  BSM m ()
setTermState t s = (terms . at @(TermMap t) t) .= Just s

addTermToDeps :: forall m t. (BSMTC m t) => TermID t -> BSM m ()
addTermToDeps t = dependencies %= G.overlay (G.vertex $ toExID t)

addTermToIdents :: forall m t. (BSMTC m t) => TermID t -> BSM m ()
addTermToIdents t = idents . at (force t) .= Just (toExID t)

runDefaultRules :: TermID t -> BSM m ()
runDefaultRules = undefined

-- | Navigates to representative and returns the termState
getTermState :: forall m t. (BSMTC m t) => TermID t -> BSM m (TermState t)
getTermState t = do
  t' <- getRepresentative t
  maybeM (panic "unreachable: we were somehow passed an unused term")
    $ use (terms . at @(TermMap t) t)

getRepresentative :: TermID t -> BSM m (TermID t)
getRepresentative = undefined

freshenTerm :: forall m t. (BSMTC m t) => t (TermID t) -> BSM m (t (TermID t))
freshenTerm = traverse getRepresentative

getDependents :: forall m t. (BSMTC m t) => ExID -> BSM m (HashSet ExID)
getDependents = undefined

getDependencies :: forall m t. (BSMTC m t) => ExID -> BSM m (HashSet ExID)
getDependencies = undefined

dependsOn :: forall m. (BSMC m) => ExID -> ExID -> BSM m ()
a `dependsOn` b = undefined

doesNotDependOn :: forall m. (BSMC m) => ExID -> ExID -> BSM m ()
a `doesNotDependOn` b = undefined

setTermValue :: forall m t. (BSMTC m t) => TermID t -> Maybe (t (TermID t)) -> BSM m ()
setTermValue = undefined

pushUpdates :: forall m. (BSMC m) => ExID -> BSM m ()
pushUpdates = undefined

redirectRelations :: forall m t. (BSMTC m t) => TermID t -> TermID t -> BSM m Bool
redirectRelations = undefined

redirectRules :: forall m t. (BSMTC m t) => TermID t -> TermID t -> BSM m Bool
redirectRules = undefined

setProperty :: forall p m t t'. (Property p t t', BSMTC m t, BSMTC m t')
            => p -> TermID t -> TermID t' -> BSM m ()
setProperty = undefined

getProperty :: forall p m t t'. (Property p t t', BSMTC m t, BSMTC m t')
            => p -> TermID t -> BSM m (Maybe (TermID t'))
getProperty = undefined

getPropMap :: forall m t. (BSMTC m t) => TermID t -> BSM m PropMap
getPropMap = undefined
-- type RAM = ReaderT Assumptions
--
-- isAssumedEqualR :: TermID t -> TermID t -> RAM m Bool
-- isAssumedEqualR = undefined
--
-- assumeEqualR :: TermID t -> TermID t -> RAM m a -> RAM m a
-- assumeEqualR = undefined
--
-- isAssumedUnifiedR :: TermID t -> TermID t -> RAM m Bool
-- isAssumedUnifiedR = undefined
--
-- assumeUnifiedR :: TermID t -> TermID t -> RAM m a -> RAM m a
-- assumeUnifiedR = undefined
--
-- isAssumedSubsumedR :: TermID t -> TermID t -> RAM m Bool
-- isAssumedSubsumedR = undefined
--
-- assumeSubsumedR :: TermID t -> TermID t -> RAM m Bool
-- assumeSubsumedR = undefined




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

instance MonadTransControl AssumeT where
  liftWith = undefined
  restoreT = undefined

instance Functor (Rule m) where
  fmap = undefined

instance Applicative (Rule m) where
  pure = undefined
