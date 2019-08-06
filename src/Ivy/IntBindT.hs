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

deriving newtype instance (Functor m) => Functor (IntBindT m)
deriving newtype instance (Monad m) => Applicative (IntBindT m)
deriving newtype instance (Monad m) => Monad (IntBindT m)
deriving newtype instance (MonadError e m) => MonadError e (IntBindT m)

monadErrEq :: forall m e. (Typeable e, MonadError e m)
  => (forall e'. (Typeable e', MonadError e' m) => e :~~: e')
monadErrEq = case eqTypeRep (typeRep @e) typeRep of
  Nothing -> panic "Functional dependency should ensure this is impossible"
  Just g -> g

instance MonadTrans IntBindT where
  lift = IntBindT . lift

instance MonadTransControl IntBindT where

  type StT IntBindT a = StT BSM a

  liftWith = defaultLiftWith IntBindT getIntBindT
  restoreT = defaultRestoreT IntBindT

type VarIB m = VarID (IntBindT m)

instance (BSEMTC e m t, Eq1 t)
         => MonadBind e (IntBindT m) t where

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

instance (MonadBind e (IntBindT m) t, BSEMTC e m t) => MonadUnify e (IntBindT m) t

instance (MonadBind e (IntBindT m) t, BSEMTC e m t) => MonadAssume e (IntBindT m) t where

  isAssumedEqual :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedEqual a b = IntBindT $ isAssumedEqualS @e @_ @t (force a) (force b)

  assumeEqual :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeEqual a b m = IntBindT $ assumeEqualS (force a) (force b) (getIntBindT m)

  isAssumedUnified :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedUnified a b = IntBindT $ isAssumedUnifiedS (force a) (force b)

  assumeUnified :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeUnified a b m = IntBindT $ assumeUnifiedS (force a) (force b) (getIntBindT m)

  isAssumedSubsumed :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedSubsumed a b = IntBindT $ isAssumedSubsumedS (force a) (force b)

  assumeSubsumed :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeSubsumed a b m = IntBindT $ assumeSubsumedS (force a) (force b) (getIntBindT m)

isAssumedEqualS :: forall e m t. (BSEMTC e m t) => TermID t -> TermID t -> BSM m Bool
isAssumedEqualS a b = do
  a' <- getRepresentative a
  b' <- getRepresentative b
  pure (a' == b')
    ||^ (view assumptions >>= hasEqAssumption a' b')
    ||^ isAssumedUnifiedS a' b'
    ||^ ( do
      mta <- lookupVarS a'
      mtb <- lookupVarS b'
      pure
        . maybe False (const True)
        . join $ (\ ta tb -> eitherToMaybe $ getTermEqualities @_ @_ @e @t ta tb) <$> mta <*> mtb
      )

isAssumedUnifiedS :: forall m t. (BSMTC m t) => TermID t -> TermID t -> BSM m Bool
isAssumedUnifiedS a b = do
  a' <- getRepresentative a
  b' <- getRepresentative b
  pure (a' == b') ||^ (view assumptions >>= hasUniAssumption a' b')

isAssumedSubsumedS :: forall m t. (BSMTC m t) => TermID t -> TermID t -> BSM m Bool
isAssumedSubsumedS a b = do
  a' <- getRepresentative a
  b' <- getRepresentative b
  pure (a' == b')
    ||^ isAssumedUnifiedS a' b'
    ||^ (view assumptions >>= hasSubAssumption a' b')
    ||^ inSubsumedSet a' b'

assumeEqualS :: forall a m t. (BSMTC m t) => TermID t -> TermID t -> BSM m a -> BSM m a
assumeEqualS a b m = local (assumptions %~ addEqAssumption a b) m

assumeUnifiedS :: forall a m t. (BSMTC m t) => TermID t -> TermID t -> BSM m a -> BSM m a
assumeUnifiedS a b m = local (assumptions %~ addUniAssumption a b) m

assumeSubsumedS :: forall a m t. (BSMTC m t) => TermID t -> TermID t -> BSM m a -> BSM m a
assumeSubsumedS a b m = local (assumptions %~ addSubAssumption a b) m

instance Functor m => Functor (RuleT e m) where
  fmap f (RLook t v k) = RLook t v (\ mt -> map f <$> k mt)
  fmap f (RBind t v a k) = RBind t v a (\ nv -> map f <$> k nv)
  fmap f (RLift as) = RLift $ map (map f) <$> as
  fmap f (RPure a)  = RPure $ f a

instance (Monad m) => Applicative (RuleT e m) where
  pure a = RPure a
  (<*>) = ap

instance (Monad m) => Monad (RuleT e m) where
  RLook t v   k >>= f = RLook t v   (\ mt -> (>>= f) <$> k mt)
  RBind t v a k >>= f = RBind t v a (\ nt -> (>>= f) <$> k nt)
  RLift as      >>= f = RLift $ map (>>= f) <$> as
  RPure a       >>= f = f a


-- | Pull out one layer of the rule as an action we can run, recurse on
--   lift operations.
evalRule :: forall a e m. (BSEMC e m) => RuleIB e m a -> RTIB e m [RuleIB e m a]
evalRule (RLook t v k) = do
    addToWatched v
    addToHistory Lookup v
    map (map force) <$> lift (lookupVar $ force v) >>= (map pure . k)

evalRule (RBind t v a k) = do
  addToModified v
  addToHistory Bind v
  term <- a v
  res :: TermID t <- force <$> (lift $ bindVar (force v) (map force term))
  pure <$> k res

evalRule (RLift as) = map mconcat . traverse evalRule =<< as

evalRule (RPure _) = pure []

instance forall e m. (MonadError e m) => MonadError e (RuleT e m) where
  throwError = lift . throwError

  catchError :: forall a. RuleT m a -> (e -> RuleT m a) -> RuleT m a
  catchError = undefined
  -- catchError (RLook t v k) a = RLook t v (\ mt -> catchError @e (k mt)
  --                                         (pure . a :: e -> RT e m (RuleT m a)))

instance MonadTrans (RuleT e) where
  lift :: (Monad m) => m a -> RuleT e m a
  lift = RLift . map (pure . RPure) . lift

instance (MonadBind e m t) => MonadBind e (RuleT e m) t where

  type Var (RuleT e m) = Var m

  freeVar = undefined
  bindVar = undefined
  lookupVar = undefined
  redirectVar = undefined

instance (MonadRule e m, Rule e m ~ RuleT e m, MonadAssume e m t)
    => MonadUnify e (RuleT e m) t where
  unify = undefined
  equals = undefined
  subsume = undefined

instance (MonadRule e m, Rule e m ~ RuleT e m, MonadAssume e m t)
  => MonadAssume e (RuleT e m) t where

  isAssumedEqual :: Var m t -> Var m t -> RuleT e m Bool
  isAssumedEqual = undefined

  assumeEqual :: Var m t -> Var m t -> RuleT e m a -> RuleT e m a
  assumeEqual = undefined

  isAssumedUnified :: Var m t -> Var m t -> RuleT e m Bool
  isAssumedUnified = undefined

  assumeUnified :: Var m t -> Var m t -> RuleT e m a -> RuleT e m a
  assumeUnified = undefined

  isAssumedSubsumed :: Var m t -> Var m t -> RuleT e m Bool
  isAssumedSubsumed = undefined

  assumeSubsumed :: Var m t -> Var m t -> RuleT e m a -> RuleT e m a
  assumeSubsumed = undefined

instance ( MonadRule e m
         , forall t. (MonadBind e (Rule e m) t) => MonadBind e m t
         , Rule e m ~ RuleT e m
         , MonadProperty e p m
         , Var m ~ Var (RuleT e m)) => MonadProperty e p (RuleT e m) where

  propertyOf :: forall t t'. (MonadBind e (RuleT m) t, MonadBind e (RuleT m) t', Property p t t')
     => p -> Var (RuleT m) t -> RuleT m (Var (RuleT m) t')
  propertyOf p v = lift $ propertyOf @e p v

instance ( Typeable e
         , forall t. (MonadBind e (IntBindT m) t) => BSEMTC e m t
         , MonadError e m)
  => MonadRule e (IntBindT m) where

  type Rule e (IntBindT m) = RuleT e (IntBindT m)

  addRule r = IntBindT $
    (newRuleMeta <$> newIdent)
      >>= insertRule r
      >>= triggerRule

instance (Monad m) => MonadFail (RuleT e m) where
  fail _ = RLift $ pure []

instance (MonadError e m) => MonadRule e (RuleT e m) where
  type Rule e (RuleT e m) = RuleT e m
  addRule = id

newIdent :: forall o m s. (MonadState s m, HasSupply s Supply, Newtype o Int)
         => m o
newIdent = map pack $ supply %%= freshId

setTermState :: forall m t. (BSMTC m t) => TermID t -> TermState t ->  BSM m ()
setTermState t s = (terms . at @(TermMap t) t) .= Just s

addTermToDeps :: forall m t. (BSMTC m t) => TermID t -> BSM m ()
addTermToDeps t = dependencies %= G.overlay (G.vertex $ toExID t)

addTermToIdents :: forall m t. (BSMTC m t) => TermID t -> BSM m ()
addTermToIdents t = idents . at (force t) .= Just (toExID t)

-- | Navigates to representative and returns the termState
getTermState :: forall m t. (BSMTC m t) => TermID t -> BSM m (TermState t)
getTermState t = do
  t' <- getRepresentative t
  maybeM (panic "unreachable: we were somehow passed an unused term")
    $ use (terms . at @(TermMap t) t)

freshenTerm :: forall m t. (BSMTC m t) => t (TermID t) -> BSM m (t (TermID t))
freshenTerm = traverse getRepresentative

-- | Applies the default rules to the
runDefaultRules :: TermID t -> BSM m ()
runDefaultRules = undefined

getRepresentative :: TermID t -> BSM m (TermID t)
getRepresentative = undefined

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

inSubsumedSet :: forall m t. (BSMTC m t) => TermID t -> TermID t -> BSM m Bool
inSubsumedSet = undefined

getTermEqualities :: forall a b e t. (Traversable t, JoinSemiLattice1 e t)
  => t a -> t b -> Either e [(a,b)]
getTermEqualities a b = catThese . foldMap (:[]) <$> liftLatJoin a b

getPropMap :: forall m t. (BSMTC m t) => TermID t -> BSM m PropMap
getPropMap = undefined

addEqAssumption :: forall t. (BSTC t)
  => TermID t -> TermID t -> Assumptions -> Assumptions
addEqAssumption = undefined

hasEqAssumption :: TermID t -> TermID t -> Assumptions -> BSM m Bool
hasEqAssumption = undefined

addUniAssumption :: forall t. (BSTC t)
  => TermID t -> TermID t -> Assumptions ->  Assumptions
addUniAssumption = undefined

hasUniAssumption :: TermID t -> TermID t -> Assumptions -> BSM m Bool
hasUniAssumption = undefined

addSubAssumption :: forall t. (BSTC t)
  => TermID t -> TermID t -> Assumptions -> Assumptions
addSubAssumption = undefined

hasSubAssumption :: TermID t -> TermID t -> Assumptions -> BSM m Bool
hasSubAssumption = undefined


-- | given an initial rule, run a single step and return all the (potentially
--   new) rule
runRule :: ()
  => RuleMeta -> RuleIB e m () -> BSM m [(RuleMeta, RuleIB e m ())]
runRule = undefined

insertRule :: RuleIB e m () -> RuleMeta -> BSM m RuleID
insertRule = undefined

lookupRule :: RuleID -> BSM m (Maybe (RuleMeta, RuleIB e m ()))
lookupRule = undefined

lookupRuleHistory :: RuleHistory -> BSM m (Maybe RuleID)
lookupRuleHistory = undefined

triggerRule :: RuleID -> BSM m ()
triggerRule = undefined

addToWatched :: TermID t -> RTIB e m ()
addToWatched = undefined

addToModified :: TermID t -> RTIB e m ()
addToModified = undefined

addToHistory :: (Newtype n Int) => RuleAction -> n -> RTIB e m ()
addToHistory = undefined
