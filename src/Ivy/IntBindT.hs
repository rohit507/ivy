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
import Ivy.Assertions

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

import Data.Partition (Partition)
import qualified Data.Partition as P

import qualified Control.Monad.Fail (fail)
import Control.Monad (ap)
import Data.IORef
import Control.Concurrent.Supply

deriving newtype instance (Functor m) => Functor (IntBindT m)
deriving newtype instance (Monad m) => Applicative (IntBindT m)
deriving newtype instance (Monad m) => Monad (IntBindT m)
deriving newtype instance (MonadError e m) => MonadError e (IntBindT m)

instance MonadTrans IntBindT where
  lift = IntBindT . lift

instance MonadTransControl IntBindT where

  type StT IntBindT a = StT BSM a

  liftWith = defaultLiftWith IntBindT getIntBindT
  restoreT = defaultRestoreT IntBindT

type VarIB m = VarID (IntBindT m)

instance (BSEMTC e m t)
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

  freshenVar :: VarIB m t -> IntBindT m (VarIB m t)
  freshenVar a = IntBindT $ force <$> getRepresentative (force a)

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

instance (forall t. (BSETC e t) => (BSEMTC e m t), BSEMC e m) => MonadProperties e (IntBindT m) where


  getPropertyPairs :: forall a t. (MonadBind e (IntBindT m) t)
      => (forall t' p. (MonadUnify e (IntBindT m) t', MonadProperty e p (IntBindT m), Property p t t')
                      => p -> These (VarIB m t') (VarIB m t') -> IntBindT m a)
      -> (a -> a -> IntBindT m a)
      -> a
      -> VarIB m t -> VarIB m t -> IntBindT m a
  getPropertyPairs f mappendM mempty a b
    = IntBindT $ getPropertyPairsS f' mappendM' mempty (force a) (force b)

    where


      f' :: (forall t' p. (Property p t t', BSEMTC e m t')
                    => p -> These (TermID t') (TermID t') ->BSM m a)
      f' p t = getIntBindT $ (f p (bimap force force t) :: IntBindT m a)

      mappendM' :: a -> a -> BSM m a
      mappendM' a b = getIntBindT $ mappendM a b



getPropertyPairsS :: forall a e m t. (BSEMTC e m t)
    => (forall t' p. (Property p t t', BSEMTC e m t')
                    => p -> These (TermID t') (TermID t') ->BSM m a)
    -> (a -> a -> BSM m a)
    -> a
    ->TermID t -> TermID t -> BSM m a
getPropertyPairsS f mappend mempty a b = do
  pma <- getPropMap a
  pmb <- getPropMap b
  let theseMap :: TypeMap (OfType ())
        = TM.intersection (TM.map empty pma) pmb
      thisMap :: TypeMap (OfType ())
        = TM.difference (TM.map empty pma) theseMap
      thatMap :: TypeMap (OfType ())
        = TM.difference (TM.map empty pmb) theseMap
  these :: [a] <- catMaybes . TM.toList <$> TM.traverse (theseOp pma pmb) theseMap
  that  :: [a] <- catMaybes . TM.toList <$> TM.traverse (thatOp pma) thatMap
  this  :: [a] <- catMaybes . TM.toList <$> TM.traverse (thisOp pma) thisMap
  foldrM mappend mempty $ this <> that <> these

  where

    empty :: forall t a. (Typeable t)
       => Proxy t -> a -> ()
    empty _ _ = ()

    theseOp :: forall p. (Typeable p)
          => PropMap
          -> PropMap
          -> p
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

    thisOp :: forall p . (Typeable p)
          => PropMap
          -> p
          -> ()
          -> BSM m (Maybe a)
    thisOp rma p _ = sequenceA $ do
      (PropRel te  tp  to  t  v ) <- TM.lookup (typeRep @p) rma
      HRefl <- eqTypeRep tp (typeRep @p)
      HRefl <- eqTypeRep te (typeRep @e)
      HRefl <- eqTypeRep to (typeRep @t)
      pure $ f p (This v)

    thatOp :: forall p. (Typeable p)
          => PropMap
          -> p
          -> ()
          -> BSM m (Maybe a)
    thatOp rmb p _ = sequenceA $ do
      (PropRel te  tp  to  t  v ) <- TM.lookup (typeRep @p) rmb
      HRefl <- eqTypeRep tp (typeRep @p)
      HRefl <- eqTypeRep te (typeRep @e)
      HRefl <- eqTypeRep to (typeRep @t)
      pure $ f p (That v)

instance (MonadBind e (IntBindT m) t, BSEMTC e m t) => MonadAssume e (IntBindT m) t where

  assumeEqual :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeEqual a b (IntBindT m) = IntBindT $ assumeEqualS (force a) (force b) m

  assumeUnified :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeUnified a b (IntBindT m) = IntBindT $ assumeUnifiedS (force a) (force b) m

  assumeSubsumed :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeSubsumed a b (IntBindT m) = IntBindT $ assumeSubsumedS (force a) (force b) m

  assertEqual :: VarIB m t -> VarIB m t -> IntBindT m ()
  assertEqual a b = IntBindT $ assertions %= addEqAssertion (force a) (force b)

  assertUnified :: VarIB m t -> VarIB m t -> IntBindT m ()
  assertUnified a b = IntBindT $ assertions %= addUniAssertion (force a) (force b)

  assertSubsumed :: VarIB m t -> VarIB m t -> IntBindT m ()
  assertSubsumed a b = IntBindT $ assertions %= addSubAssertion (force a) (force b)

  isAssumedEqual :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedEqual a b = IntBindT $ do
    assert <- use assertions
    assume <- view assumptions
    pure $ isAssertedEqualL (force a) (force b) [assume, assert]

  isAssumedUnified  :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedUnified a b = IntBindT $ do
    assert <- use assertions
    assume <- view assumptions
    pure $ isAssertedEqualL (force a) (force b) [assume, assert]

  isAssumedSubsumed :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedSubsumed a b = IntBindT $ do
    assert <- use assertions
    assume <- view assumptions
    pure $ isAssertedSubsumedL (force a) (force b) [assume, assert]

assumeEqualS :: forall a m t. (BSMTC m t) => UnivID -> UnivID -> BSM m a -> BSM m a
assumeEqualS a b m = local (assumptions %~ addEqAssertion a b) m

assumeUnifiedS :: forall a m t. (BSMTC m t) => UnivID -> UnivID  -> BSM m a -> BSM m a
assumeUnifiedS a b m = local (assumptions %~ addUniAssertion a b) m

assumeSubsumedS :: forall a m t. (BSMTC m t) => UnivID -> UnivID -> BSM m a -> BSM m a
assumeSubsumedS a b m = local (assumptions %~ addSubAssertion a b) m




instance ( forall t. (MonadBind e (IntBindT m) t) => BSEMTC e m t
         , BSEMC e m)
  => MonadRule e (IntBindT m) where

  type Rule (IntBindT m) = RuleT (IntBindT m)

  addRule = IntBindT . addRuleS

addRuleS :: (BSMC m) => RuleIB m () -> BSM m ()
addRuleS r = do
  rid :: RuleID <- newIdent
  insertRule (newRuleMeta rid) r >>= triggerRule

instance Functor m => Functor (RuleT m) where
  fmap f (RLook t v k) = RLook t v (\ mt -> map f <$> k mt)
  fmap f (RLift as) = RLift $ map (map f) <$> as
  fmap f (RPure a)  = RPure $ f a

instance (Monad m) => Applicative (RuleT m) where
  pure a = RPure a
  (<*>) = ap

instance (Monad m) => Monad (RuleT m) where
  RLook t v   k >>= f = RLook t v   (\ mt -> (>>= f) <$> k mt)
  RLift as      >>= f = RLift $ map (>>= f) <$> as
  RPure a       >>= f = f a

-- | Pull out one layer of the rule as an action we can run, recurse on
--   lift operations.
evalRule :: forall a m. (Monad m) => RuleIB m a -> RTIB m [RuleIB m a]
evalRule (RLook _ v k) = do
  addToWatched (force v)
  lift (lookupVar v) >>= (map pure . k)

evalRule (RLift as) = map mconcat . traverse evalRule =<< as

evalRule (RPure _) = pure []

-- | FIXME :: `catchError` does nothing in the current instance, since
--            it requires us to be able to unify the inner and outer error type.
instance (MonadError e m) => MonadError e (RuleT m) where
  throwError = lift . throwError

  catchError m _ = m
  -- catchError (RLook t v k) r   = RLook t v (\ mt -> catchError (k mt) (pure . r))
  -- catchError (RBind t v a k) r = RBind t v a (\ nt -> catchError (k nt) (pure . r))
  -- catchError (RLift as) r      = RLift $ map (\ a -> catchError a r) <$> as

instance MonadTrans RuleT where
  lift = RLift . map (pure . RPure) . lift

instance (MonadBind e m t) => MonadBind e (RuleT m) t where

  type Var (RuleT m) = Var m

  freeVar = lift freeVar

  bindVar a b = lift $ bindVar a b

  lookupVar a = RLook typeRep a (pure . pure)

  redirectVar a b = lift $ redirectVar a b

  freshenVar = lift . freshenVar

instance (MonadRule e m, Rule m ~ RuleT m, Newtype (Var m t) Int,  MonadAssume e m t) => MonadAssume e (RuleT m) t where

  assumeEqual :: Var m t -> Var m t -> RuleT m a -> RuleT m a
  assumeEqual a b m = RLift $ do
    old <- use @RuleMeta assumptions
    assumptions %= addEqAssertion (force a) (force b)
    rtDrop $ do
     a <- m
     rtLift $ assumptions .= old
     pure a

  assumeUnified :: Var m t -> Var m t -> RuleT m a -> RuleT m a
  assumeUnified a b m = RLift $ do
    old <- use @RuleMeta assumptions
    assumptions %= addUniAssertion (force a) (force b)
    rtDrop $ do
     a <- m
     rtLift $ assumptions .= old
     pure a

  assumeSubsumed :: Var m t -> Var m t -> RuleT m a -> RuleT m a
  assumeSubsumed a b m = RLift $ do
    old <- use @RuleMeta assumptions
    assumptions %= addSubAssertion (force a) (force b)
    rtDrop $ do
     a <- m
     rtLift $ assumptions .= old
     pure a

  assertEqual :: Var m t -> Var m t -> RuleT m ()
  assertEqual a b = lift $ assertEqual a b

  assertUnified :: Var m t -> Var m t -> RuleT m ()
  assertUnified a b = lift $ assertUnified a b

  assertSubsumed :: Var m t -> Var m t -> RuleT m ()
  assertSubsumed a b = lift $ assertSubsumed a b

  isAssumedEqual :: Var m t -> Var m t -> RuleT m Bool
  isAssumedEqual a b = RLift $ do
    assumed :: Assertions Int <- use assumptions
    pure . pure $ do
      let a' = getRep (force a) assumed
          b' = getRep (force b) assumed
      pure (isAssertedEqual a' b' assumed)
        ||^ (lift $ isAssumedEqual @_ @_ @t (force a') (force b'))

  isAssumedUnified :: Var m t -> Var m t -> RuleT m Bool
  isAssumedUnified a b = RLift $ do
    assumed :: Assertions Int <- use assumptions
    pure . pure $ do
      let a' = getRep (force a) assumed
          b' = getRep (force b) assumed
      pure (isAssertedUnified a' b' assumed)
        ||^ (lift $ isAssumedUnified @_ @_ @t (force a') (force b'))

  -- | It is unclear is this is
  isAssumedSubsumed :: Var m t -> Var m t -> RuleT m Bool
  isAssumedSubsumed a b = RLift $ do
    assumed :: Assertions Int <- use assumptions
    pure . pure $ do
      let a' = getRep (force a) assumed
          b' = getRep (force b) assumed
      pure (isAssertedSubsumed a' b' assumed)
        ||^ (lift $ isAssumedSubsumed @_ @_ @t (force a') (force b'))

instance ( MonadRule e m
         , forall t. (MonadBind e (Rule m) t) => MonadBind e m t
         , Rule m ~ RuleT m
         , MonadProperty e p m
         , Var m ~ Var (RuleT m)) => MonadProperty e p (RuleT m) where

  propertyOf :: forall t t'. (MonadBind e (RuleT m) t, MonadBind e (RuleT m) t', Property p t t')
     => p -> Var (RuleT m) t -> RuleT m (Var (RuleT m) t')
  propertyOf p v = lift $ propertyOf @e p v

instance (MonadProperties e m
         , forall t. MonadBind e (RuleT m) t => MonadBind e m t
         , forall p. MonadProperty e p (RuleT m) => MonadProperty e p m
         , MonadRule e m
         , Rule m ~ RuleT m
         , Var m ~ Var (RuleT m)
         ) => MonadProperties e (RuleT m) where

  getPropertyPairs :: forall a t. (MonadBind e (RuleT m) t)
      => (forall t' p. (MonadUnify e (RuleT m) t', MonadProperty e p (RuleT m), Property p t t')
                      => p -> These (Var m t') (Var m t') -> RuleT m a)
      -> (a -> a -> RuleT m a)
      -> a
      -> Var m t -> Var m t -> RuleT m a
  getPropertyPairs f append empty a b = RLift $ do
    r :: [RuleT m a] <- lift $ getPropertyPairs
        (\ p t -> pure . pure $ f p t)
        (\ a b -> pure $ a <> b)
        [] a b
    rtDrop $ foldrM append empty =<< sequenceA r

instance (Monad m) => MonadFail (RuleT m) where
  fail _ = RLift $ pure []

instance (MonadError e m) => MonadRule e (RuleT m) where
  type Rule (RuleT m) = RuleT m
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
  maybeM (panic "unreachable: we were somehow passed an unused term")
    $ use (terms . at @(TermMap t) t)

freshenTerm :: forall m t. (BSMTC m t) => t (TermID t) -> BSM m (t (TermID t))
freshenTerm = traverse getRepresentative

-- | Applies the default rules to the given term
runDefaultRules :: forall m t. (BSMTC m t) => TermID t -> BSM m ()
runDefaultRules t = do
  mrs <- TM.lookup (typeRep @(Term t)) <$> (use defaultRules :: BSM m (RuleMap))
  case mrs of
    Nothing -> skip
    Just (DefaultRule _ tm rs) -> case eqTypeRep tm (typeRep @(IntBindT m)) of
      Nothing -> panic "unreachable"
      Just HRefl -> sequenceA_ $ map
          (\ f -> addRuleS $ f (force @(VarIB m t) t))
          rs

addDefaultRule :: forall e m t. (BSEMTC e m t, MonadRule e (IntBindT m)) => (VarIB m t -> RuleIB m ()) -> BSM m ()
addDefaultRule r = do
  ts <- getAllTerms @m @t
  sequenceA_ $ map
      (\ t -> addRuleS $ r (force @(VarIB m t) t))
          ts
  insertDefaultRule r

insertDefaultRule :: forall e m t. (BSEMTC e m t, MonadRule e (IntBindT m)) => (VarIB m t -> RuleIB m ()) -> BSM m ()
insertDefaultRule r = (TM.lookup (typeRep @(Term t)) <$> use defaultRules) >>= \case
  Nothing -> defaultRules %= TM.insert (typeRep @(Term t))
    (DefaultRule (typeRep @e) (typeRep @(IntBindT m)) [r] :: DefaultRule t)
  Just (DefaultRule te tm rs) -> maybe (panic "unreachable") id $ do
    HRefl <- eqTypeRep te (typeRep @e)
    HRefl <- eqTypeRep tm (typeRep @(IntBindT m))
    pure $ defaultRules %= TM.insert (typeRep @(Term t))
           (DefaultRule te (typeRep @(IntBindT m)) (r:rs) :: DefaultRule t)

getAllTerms :: forall m t. (BSMTC m t) => BSM m [TermID t]
getAllTerms = (TM.lookup (typeRep @(Term t)) . getTermMap . (getTMap :: TMap -> TermMap t) <$> use terms_) >>= \case
  Nothing -> pure []
  Just hm -> pure $ HM.keys hm

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

-- | given an initial rule, run a single step and return all the (potentially
--   new) rule.
runRule :: ()
  => RuleMeta -> RuleIB m () -> BSM m [(RuleMeta, RuleIB m ())]
runRule = undefined

-- | History aware lookup of rules.
insertRule :: RuleMeta -> RuleIB m () -> BSM m RuleID
insertRule = undefined

lookupRule :: RuleID -> BSM m (Maybe (RuleMeta, RuleIB m ()))
lookupRule = undefined

lookupRuleHistory :: RuleHistory -> BSM m (Maybe RuleID)
lookupRuleHistory = undefined

triggerRule :: RuleID -> BSM m ()
triggerRule = undefined

addToWatched :: TermID t -> RTIB m ()
addToWatched = undefined
