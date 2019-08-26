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

module Ivy.IntBindT
  ( BSEMTC
  , IntBindT()
  , Config(..)
  , runIntBindT
  , addDefaultRule
  ) where

import Intro hiding (Item)
import Ivy.Prelude
-- import Control.Lens hiding (Context)
-- import Control.Lens.TH

-- import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.IntBindTTypes
import Ivy.Assertions

-- import Data.Bimap (Bimap)
-- import qualified Data.Bimap as BM
import Data.TypeMap.Dynamic (TypeMap, OfType)
import qualified Data.TypeMap.Dynamic as TM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import qualified GHC.Base (fmap)
-- import Algebra.Graph.AdjacencyMap (AdjacencyMap)
import qualified Algebra.Graph.AdjacencyMap as G
import qualified Data.Set as S


-- import Data.Partition (Partition)
-- import qualified Data.Partition as P

import qualified Control.Monad.Fail (fail)
import Control.Monad (ap)
-- import Data.IORef
-- import Control.Concurrent.Supply

deriving newtype instance (Functor m) => Functor (IntBindT m)
deriving newtype instance (Monad m) => Applicative (IntBindT m)
deriving newtype instance (Monad m) => Monad (IntBindT m)
deriving newtype instance (MonadError e m) => MonadError e (IntBindT m)
deriving newtype instance (MonadIO m) => MonadIO (IntBindT m)


instance MonadTrans IntBindT where
  lift = IntBindT . lift

instance MonadTransControl IntBindT where

  type StT IntBindT a = StT BSM a

  liftWith = defaultLiftWith IntBindT getIntBindT
  restoreT = defaultRestoreT IntBindT

type VarIB m = VarID (IntBindT m)

instance (BSEMTC e m r)
         => MonadBind e (IntBindT m) r where

  type Var (IntBindT m) = VarID (IntBindT m)

  freeVar :: IntBindT m (VarIB m r)
  freeVar = IntBindT $ force @(VarIB m r) <$> (freeVarS @m @r)

  lookupVar :: VarIB m r -> IntBindT m (Maybe (r (VarIB m r)))
  lookupVar
    = IntBindT
    . map (map . map $ force @(VarIB m r))
    . lookupVarS @m @r
    . force @(TermID r)

  bindVar :: VarIB m r -> r (VarIB m r) -> IntBindT m (VarIB m r)
  bindVar v t = IntBindT $ force <$> (bindVarS (force v) $ map force t)

  redirectVar :: VarIB m r -> VarIB m r -> IntBindT m (VarIB m r)
  redirectVar a b = IntBindT $ force <$> redirectVarS @e @m @r (force a) (force b)

  freshenVar :: VarIB m r -> IntBindT m (VarIB m r)
  freshenVar a = IntBindT $ force <$> getRepresentative (force @(TermID r) a)

freeVarS :: forall m t. (BSMTC m t) =>  BSM m (TermID t)
freeVarS = do
  nv :: TermID t <- newIdent
  traceShowM ('f', nv)
  setTermState nv freeTermState
  addTermToDeps nv
  addTermToIdents nv
  runDefaultRules nv
  pure nv

lookupVarS :: forall m t. (BSMTC m t) => TermID t -> BSM m (Maybe (t (TermID t)))
lookupVarS t = getRepresentative t >>= getTermState >>= \case
  Forwarded _ -> panic "Unreachable: getRepresentative always returns bound term."
  Bound bs  -> traverse freshenTerm (bs ^. termValue)

bindVarS :: forall m t. (BSMTC m t) => TermID t -> t (TermID t) -> BSM m (TermID t)
bindVarS v t = do
  mot <- lookupVarS v
  nt  <- freshenTerm t
  traceShowM =<< (('b','p',v,) <$> use ruleHistories)
  -- traceShowM =<< (('b','d',) <$> use dependencies)
  depChange <- map (fromMaybe False) . whenJust mot $ \ ot -> do
    let otd = foldMap (HS.singleton . toExID) ot
        ntd = foldMap (HS.singleton . toExID) nt
        tv = toExID v
        lostDeps = HS.difference otd ntd
        newDeps  = HS.difference ntd otd
    -- traceShowM =<< (('b','a',) <$> use ruleHistories)
    unless (HS.null lostDeps) $
      traverse_ (tv `doesNotDependOn`) $ HS.toList lostDeps
    -- traceShowM =<< (('b','b',) <$> use ruleHistories)
    unless (HS.null newDeps) $
      traverse_ (tv `dependsOn`) $ HS.toList newDeps
    -- traceShowM =<< (('b','c',) <$> use ruleHistories)
    pure $ HS.null lostDeps || HS.null newDeps
  -- traceShowM =<< (('b','d',) <$> use ruleHistories)
  v' <- getRepresentative v
  setTermValue v' $ Just nt
  -- traceShowM =<< (('b','e',) <$> use ruleHistories)
  -- When the term has changed in some salient way we need to push updates.
  let dirty = depChange ||
                (not . fromMaybe False $ (liftEq (==)) <$> (Just nt) <*> mot)
  when (traceShowId dirty) $ do
    traceShowM =<< (('b','1',) <$> use ruleHistories)
    -- traceShowM =<< (('b','d',) <$> use dependencies)
    pushUpdates . toExID =<< getRepresentative v'
    traceShowM =<< (('b','2',) <$> use ruleHistories)
    -- traceShowM =<< (('b','d',) <$> use dependencies)
  getRepresentative v'

-- | TODO :: Fix this, It's not doing sensible things
redirectVarS :: forall e m t. (BSEMTC e m t) => TermID t -> TermID t -> BSM m (TermID t)
redirectVarS old new = do
  o' <- getRepresentative old
  n' <- getRepresentative new
  redirectRelations @e o' n'
  redirectRules o' n'
  when (o' /= n') $ do
    let to' = toExID o'
        tn' = toExID n'
    -- Move depends from old to new
    getDependencies @m to' >>= traverse_ (manageDependencies to' tn')
    getDependents   @m tn' >>= traverse_ (manageDependents   to' tn')
    to' `dependsOn` tn'
    -- lookupVarS o' >>= setTermValue n'
    setTermState o' $ Forwarded n'
    pushUpdates tn'
  getRepresentative n'

  where

    manageDependencies old new dep = do
      dep `doesNotDependOn` old
      dep `dependsOn`       new

    manageDependents old new dep = do
      old `doesNotDependOn` dep
      new `dependsOn`       dep

instance (forall t. (BSETC e t) => (BSEMTC e m t), BSEMC e m,
         Property p, MonadBind e (IntBindT m) (From p), MonadBind e (IntBindT m) (To p))
         => MonadProperty e p (IntBindT m) where

  propertyOf :: (From p ~ t, BSEMTC e m (From p), BSEMTC e m (To p), Property p)
      => p -> VarIB m t -> IntBindT m (VarIB m (To p))
  propertyOf p var = IntBindT $ force <$> propertyOfS p (force var)

propertyOfS :: forall e p m. (Property p, BSEMTC e m (From p), BSEMTC e m (To p))
            => p -> TermID (From p) -> BSM m (TermID (To p))
propertyOfS _ v = {- traceShow ('o', v, typeRep @p) $ -} getProperty @e (typeRep @p) v >>= \case
  Nothing -> do
    r :: TermID (To p) <- freeVarS
    setProperty @e (typeRep @p) v r
    traceShowM ('p',r)
    pure r
  Just r -> pure r

instance (BSEMC e m) => MonadProperties e (IntBindT m) where


  getPropertyPairs :: forall a t. (MonadBind e (IntBindT m) t)
      => (forall p proxy. ( From p ~ t
                         , MonadAssume e (IntBindT m) (To p)
                         , MonadProperty e p (IntBindT m), Property p)
                      => proxy p -> These (VarIB m (To p)) (VarIB m (To p)) -> IntBindT m a)
      -> (a -> a -> IntBindT m a)
      -> a
      -> VarIB m t -> VarIB m t -> IntBindT m a
  getPropertyPairs f mappendM mempty a b
    = IntBindT $ getPropertyPairsS @a @_ @_ @t f' mappendM' mempty (force a) (force b)

    where


      f' :: (forall p proxy. (From p ~ t, Property p, BSEMTC e m (To p))
                    => proxy p -> These (TermID (To p)) (TermID (To p)) ->BSM m a)
      f' p t = getIntBindT $ (f p (bimap force force t) :: IntBindT m a)

      mappendM' :: a -> a -> BSM m a
      mappendM' a b = getIntBindT $ mappendM a b


getPropertyPairsS :: forall a e m t. (BSEMC e m, BSTC t)
    => (forall p proxy. (From p ~ t, Property p, BSEMTC e m (To p))
                    => proxy p -> These (TermID (To p)) (TermID (To p)) ->BSM m a)
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
  these :: [a] <- catMaybes . TM.toList <$> TM.traverse (theseOp pma pmb) theseMap
  that  :: [a] <- catMaybes . TM.toList <$> TM.traverse (thatOp  pma) thatMap
  this  :: [a] <- catMaybes . TM.toList <$> TM.traverse (thisOp  pma) thisMap
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
    theseOp rma rmb p _ = sequenceA $ {- traceshow ('t', a,b,typerep @p) $-} do
      (PropRel te  tp  v ) <- TM.lookup (typeRep @p) rma
      (PropRel te' tp' v') <- TM.lookup (typeRep @p) rmb
      HRefl <- eqTypeRep tp tp'
      HRefl <- eqTypeRep tp (typeRep @p)
      HRefl <- eqTypeRep te te'
      HRefl <- eqTypeRep te (typeRep @e)
      HRefl <- eqTypeRep (typeRep @(From p)) (typeRep @t)
      pure $ f p (These v v')

    thisOp :: forall p proxy. (Typeable p)
          => PropMap
          -> proxy p
          -> ()
          -> BSM m (Maybe a)
    thisOp rma p _ = sequenceA $ do
      (PropRel te  tp  v ) <- TM.lookup (typeRep @p) rma
      HRefl <- eqTypeRep tp (typeRep @p)
      HRefl <- eqTypeRep te (typeRep @e)
      HRefl <- eqTypeRep (typeRep @(From p)) (typeRep @t)
      pure $ f p (This v)

    thatOp :: forall p proxy. (Typeable p)
          => PropMap
          -> proxy p
          -> ()
          -> BSM m (Maybe a)
    thatOp rmb p _ = sequenceA $ do
      (PropRel te  tp  v ) <- TM.lookup (typeRep @p) rmb
      HRefl <- eqTypeRep tp (typeRep @p)
      HRefl <- eqTypeRep te (typeRep @e)
      HRefl <- eqTypeRep (typeRep @(From p)) (typeRep @t)
      pure $ f p (That v)




instance (MonadBind e (IntBindT m) t, BSEMTC e m t) => MonadAssume e (IntBindT m) t where

  assumeEqual :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeEqual a b (IntBindT m) = IntBindT $
    assumeEqualS @_ @_ @t (toSomeVar @(IntBindT m) a) (toSomeVar @(IntBindT m) b) m

  assumeUnified :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeUnified a b (IntBindT m) = IntBindT $
    assumeUnifiedS @_ @_ @t (toSomeVar @(IntBindT m) a) (toSomeVar @(IntBindT m) b) m

  assumeSubsumed :: VarIB m t -> VarIB m t -> IntBindT m a -> IntBindT m a
  assumeSubsumed a b (IntBindT m) = IntBindT $
    assumeSubsumedS @_ @_ @t (toSomeVar @(IntBindT m) a) (toSomeVar @(IntBindT m) b) m


  assertEqual :: VarIB m t -> VarIB m t -> IntBindT m ()
  assertEqual a b = IntBindT $
    assertions %= addEqAssertion (toSomeVar @(IntBindT m) a) (toSomeVar @(IntBindT m) b)

  assertUnified :: VarIB m t -> VarIB m t -> IntBindT m ()
  assertUnified a b = IntBindT $
    assertions %= addUniAssertion (toSomeVar @(IntBindT m) a) (toSomeVar @(IntBindT m) b)


  assertSubsumed :: VarIB m t -> VarIB m t -> IntBindT m ()
  assertSubsumed a b = IntBindT $
    assertions %= addSubAssertion (toSomeVar @(IntBindT m) a) (toSomeVar @(IntBindT m) b)

  isAssumedEqual :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedEqual a b = IntBindT $ do
    assert <- use assertions
    assume <- view assumptions
    pure $ isAssertedEqualL
             (toSomeVar @(IntBindT m) a)
             (toSomeVar @(IntBindT m) b) [assume, assert]

  isAssumedUnified  :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedUnified a b = IntBindT $ do
    assert <- use assertions
    assume <- view assumptions
    pure $ isAssertedUnifiedL
             (toSomeVar @(IntBindT m) a)
             (toSomeVar @(IntBindT m) b) [assume, assert]

  isAssumedSubsumed :: VarIB m t -> VarIB m t -> IntBindT m Bool
  isAssumedSubsumed a b = IntBindT $ do
    assert <- use assertions
    assume <- view assumptions
    pure $ isAssertedSubsumedL
             (toSomeVar @(IntBindT m) a)
             (toSomeVar @(IntBindT m) b) [assume, assert]

assumeEqualS :: forall a m t. (BSMTC m t) => SomeVar -> SomeVar -> BSM m a -> BSM m a
assumeEqualS a b m = local (assumptions %~ addEqAssertion a b) m

assumeUnifiedS :: forall a m t. (BSMTC m t) => SomeVar -> SomeVar  -> BSM m a -> BSM m a
assumeUnifiedS a b m = local (assumptions %~ addUniAssertion a b) m

assumeSubsumedS :: forall a m t. (BSMTC m t) => SomeVar -> SomeVar -> BSM m a -> BSM m a
assumeSubsumedS a b m = local (assumptions %~ addSubAssertion a b) m

instance (BSEMC e m) => MonadRule e (IntBindT m) where

  type Rule (IntBindT m) = RuleT (IntBindT m)

  addRule = IntBindT . addRuleS

addRuleS :: (BSMC m) => RuleIB m () -> BSM m ()
addRuleS r = do
  rid :: RuleID <- newIdent
  traceShowM =<< (('a','1',rid,) <$> use ruleHistories)
  insertRule (newRuleMeta rid) r >>= triggerRule
  traceShowM =<< (('a','2',) <$> use ruleHistories)


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

-- FIXME :: So the issue here is that, in the generation of the rule we execute
--         a portion of the internal structure, while not building a proper
--         log of actions. in effect, the RuleIBs we return don't have the
--         parent action information. I think the only way to do this properly
--         is to refactor our evalRule into something more like a continuation
--         monad, were we build up an inner sequence of actions.

-- | Pull out one layer of the rule as an action we can run, recurse on
--   lift operations.
evalRule :: forall a m. (BSMC m) => RuleIB m a -> RTIB m [RuleIB m a]
evalRule (RLook _ v k) = do
  traceM $ "Running Rule Look " <> show  v
  addToWatched (forceTID v)
  term <- lift (lookupVar $ force v)
  pure <$> k term

evalRule (RLift as) = do
  map mconcat . join $ sequenceA . map evalRule <$> as

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

instance ( MonadRule e m
         , Rule m ~ RuleT m
         , MonadAssume e m t
         , Typeable m
         ) => MonadAssume e (RuleT m) t where

  assumeEqual :: Var m t -> Var m t -> RuleT m a -> RuleT m a
  assumeEqual a b m = RLift $ do
    old <- use @RuleMeta assumptions
    assumptions %= addEqAssertion (toSomeVar @m a) (toSomeVar @m b)
    rtDrop $ do
     a <- m
     rtLift $ assumptions .= old
     pure a

  assumeUnified :: Var m t -> Var m t -> RuleT m a -> RuleT m a
  assumeUnified a b m = RLift $ do
    old <- use @RuleMeta assumptions
    assumptions %= addUniAssertion (toSomeVar @m a) (toSomeVar @m b)
    rtDrop $ do
     a <- m
     rtLift $ assumptions .= old
     pure a

  assumeSubsumed :: Var m t -> Var m t -> RuleT m a -> RuleT m a
  assumeSubsumed a b m = RLift $ do
    old <- use @RuleMeta assumptions
    assumptions %= addSubAssertion (toSomeVar @m a) (toSomeVar @m b)
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
    assumed :: Assertions SomeVar <- use assumptions
    pure . pure $ do
      let a' = getRep (toSomeVar @m a) assumed
          b' = getRep (toSomeVar @m b) assumed
      pure (isAssertedEqual a' b' assumed)
        ||^ (liftAssumed @m @t isAssumedEqual a' b')

  isAssumedUnified :: Var m t -> Var m t -> RuleT m Bool
  isAssumedUnified a b = RLift $ do
    assumed :: Assertions SomeVar <- use assumptions
    pure . pure $ do
      let a' = getRep (toSomeVar @m a) assumed
          b' = getRep (toSomeVar @m b) assumed
      pure (isAssertedUnified a' b' assumed)
        ||^ (liftAssumed @m @t isAssumedUnified a' b')

  -- | It is unclear is this is
  isAssumedSubsumed :: Var m t -> Var m t -> RuleT m Bool
  isAssumedSubsumed a b = RLift $ do
    assumed :: Assertions SomeVar <- use assumptions
    pure . pure $ do
      let a' = getRep (toSomeVar @m a) assumed
          b' = getRep (toSomeVar @m b) assumed
      pure (isAssertedSubsumed a' b' assumed)
        ||^ (liftAssumed @m @t isAssumedSubsumed a' b')

liftAssumed :: forall m t d. (Typeable m, Typeable t)
  => (Var m t -> Var m t -> d) -> SomeVar -> SomeVar -> d
liftAssumed f (SomeVar tm tt v) (SomeVar tm' tt' v')
  = fromMaybe (panic "undefined") $ do
        HRefl <- eqTypeRep tm tm'
        HRefl <- eqTypeRep tm (typeRep @m)
        HRefl <- eqTypeRep tt tt'
        HRefl <- eqTypeRep tt (typeRep @t)
        pure $ f v v'


instance ( MonadRule e m
         , forall t. (MonadBind e (Rule m) t) => MonadBind e m t
         , Rule m ~ RuleT m
         , MonadProperty e p m
         , Var m ~ Var (RuleT m)) => MonadProperty e p (RuleT m) where

  propertyOf :: (MonadBind e (RuleT m) (From p), MonadBind e (RuleT m) (To p), Property p)
     => p -> Var (RuleT m) (From p) -> RuleT m (Var (RuleT m) (To p))
  propertyOf p v = lift $ propertyOf @e p v

instance (MonadProperties e m
         , forall t. MonadBind e (RuleT m) t => MonadBind e m t
         , forall p. MonadProperty e p (RuleT m) => MonadProperty e p m
         , MonadRule e m
         , Typeable m
         , Rule m ~ RuleT m
         , Var m ~ Var (RuleT m)
         ) => MonadProperties e (RuleT m) where

  getPropertyPairs :: forall a t. (MonadBind e (RuleT m) t)
      => (forall p proxy. (From p ~ t
                         , MonadAssume e (RuleT m) (To p)
                         , MonadProperty e p (RuleT m)
                         , Property p)
                      => proxy p -> These (Var m (To p)) (Var m (To p)) -> RuleT m a)
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

instance (MonadRule e m) => MonadRule e (RuleT m) where
  type Rule (RuleT m) = RuleT m
  addRule = id

newIdent :: forall o m s. (Show o, MonadState s m, HasSupply s Supply, Newtype o Int)
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

getRepresentative :: forall m t. (BSMTC m t) => TermID t -> BSM m (TermID t)
getRepresentative t = use (terms . at @(TermMap t) t) >>= \case
  Nothing -> panic "should be impossible to generate uninstanciated termID"
  Just (Forwarded t') -> do
    rep <- getRepresentative t'
    (terms . at @(TermMap t) t) .= Just (Forwarded rep)
    pure rep
  Just _ -> pure t

getDependents :: forall m. (BSMC m) => ExID -> BSM m (HashSet ExID)
getDependents a = HS.fromList . S.toList . G.postSet a <$> use dependencies

getDependencies :: forall m. (BSMC m) => ExID -> BSM m (HashSet ExID)
getDependencies a = HS.fromList . S.toList . G.preSet a <$> use dependencies

dependsOn :: forall m. (BSMC m) => ExID -> ExID -> BSM m ()
a `dependsOn` b = dependencies %= G.overlay (G.edge b a)

doesNotDependOn :: forall m. (BSMC m) => ExID -> ExID -> BSM m ()
a `doesNotDependOn` b = dependencies %= G.removeEdge b a

setTermValue :: forall m t. (BSMTC m t) => TermID t -> Maybe (t (TermID t)) -> BSM m ()
setTermValue t v = do
  t' <- getRepresentative t
  use (terms . at @(TermMap t) t') >>= \case
    Nothing -> panic "unreachable"
    Just (Bound s) ->
      (terms . at @(TermMap t) t') .= (Just $ Bound (set termValue v s))
    Just _ -> panic "unreachable"

pushUpdates :: forall m. (BSMC m) => ExID -> BSM m ()
pushUpdates e = traceShow ('v', showExID e) $ do
  case e of
    (RID r) -> traceShow e $ triggerRule r
    _ -> pure ()
  deps <- getDependents @m e
  traceShowM ('p', e, deps)
  traverse_ pushUpdates deps

-- getTermEqualities :: forall a b e t. (Traversable t, JoinSemiLattice1 e t)
--   => t a -> t b -> Either e [(a,b)]
-- getTermEqualities a b = catThese . foldMap (:[]) <$> liftLatJoin a b

-- | Go through all the relations of term a and redirect them to the corresponding
--   relations for term b. Return whether changes were made.
--
--   This mostly assumes that unification and redirection of the relations
--   before hand. It only redirects.
redirectRelations :: forall e m t. (BSEMTC e m t) => TermID t -> TermID t -> BSM m Bool
redirectRelations o n = {-traceShow ('r',o,n) $-} getPropertyPairsS f' mappendM' False o n

  where

      f' :: (forall p proxy. (From p ~ t, Property p, BSEMTC e m (To p))
                    => proxy p -> These (TermID (To p)) (TermID (To p)) -> BSM m Bool)
      f' _ (That _) = pure False
      f' p (This o') = {- traceShow ('1', o') $ -} do
        setProperty p n o'
        pure False
      f' _ (These o' n') = {- traceShow ('2', o',n') $ -} do
        redirectVarS o' n'
        pure True

      mappendM' :: Bool -> Bool -> BSM m Bool
      mappendM' a b = pure $ a || b


-- | traverse the rule histories unifying the two terms, and turning any
--   conflicts into redirections. Return if changes where made.
--
--   This will assume that two rules with the same history are functionally
--   identical.
redirectRules :: forall m t. (BSMTC m t) => TermID t -> TermID t -> BSM m Bool
redirectRules o n = do
  rh <- use ruleHistories
  traceM $ "Redirecting rule " <> show o <> " to " <> show n
  res <- traverse mergeRuleHistories rh
  traceShowM =<< (('3',) <$> use ruleHistories)
  ruleHistories .= map snd res
  traceShowM =<< (('4',) <$> use ruleHistories)
  pure (foldr (||) False . map fst $ res)

  where

    -- | If there are old and new members, we redirect them and merge their
    --   subtrees.
    mergeRuleHistMap :: HashMap ExID RuleHistories
                       -> BSM m (Bool, HashMap ExID RuleHistories)
    mergeRuleHistMap hm = do
      let mo = (^. term) =<< HM.lookup (toExID o) hm
          mn = (^. term) =<< HM.lookup (toExID n) hm
      d <- fromMaybe False <$> sequenceA (redirectRule <$> mo <*> mn)
      updates <- traverse mergeRuleHistories hm
      let dirty  = d || (foldr (||) False . map fst $ updates)
          result = map snd $ updates
      pure (dirty, result)


    mergeRuleHistories ::  RuleHistories -> BSM m (Bool, RuleHistories)
    mergeRuleHistories (RuleHistories t ns) = do
      (d, ns') <- mergeRuleHistMap ns
      t' <- traverse getRuleRep t
      pure (d, RuleHistories t' ns')


    -- | redirect a single rule, just updates things.
    redirectRule :: RuleID -> RuleID -> BSM m Bool
    redirectRule o n = do
      o' <- getRuleRep o
      n' <- getRuleRep n
      if (o' == n')
      then (pure False)
      else ((rules . at o .= Just (Merged n)) *> pure True)


setProperty :: forall e p m proxy. (Property p, BSEMTC e m (From p), BSEMTC e m (To p))
            => proxy p -> TermID (From p) -> TermID (To p) -> BSM m ()
setProperty _ term prop = {- traceShow ('s', term,prop, typeRep @p) $ -} do
  term' <- getRepresentative term
  prop' <- getRepresentative prop
  (terms . at @(TermMap (From p)) term') %= \case
    Nothing -> panic "unreachable"
    Just (Forwarded _) -> panic "unreachable"
    Just (Bound bs) -> Just . Bound $ (properties %~ (TM.insert (typeRep @p)
        (PropRel (typeRep @e) (typeRep @p) prop'))) bs

getProperty :: forall e p m proxy. (Property p, BSEMTC e m (From p), BSEMTC e m (To p))
            => proxy p -> TermID (From p) -> BSM m (Maybe (TermID (To p)))
getProperty _ term = do
  res <- TM.lookup (typeRep @p) <$> getPropMap term
  o <- pure $ {- traceShow ('g', term, res, typeRep @p) $ -} res >>= \ (PropRel te tp tid) -> do
    HRefl <- eqTypeRep te (typeRep @e)
    HRefl <- eqTypeRep tp (typeRep @p)
    pure tid
  sequenceA $ getRepresentative <$> o

getPropMap :: forall m t. (BSMTC m t) => TermID t -> BSM m PropMap
getPropMap t = do
  t' <- getRepresentative t
  use (terms . at @(TermMap t) t') >>= \case
    Nothing -> panic "unreachable"
    Just (Forwarded _) -> panic "unreachable"
    Just (Bound bs) -> pure (bs ^. properties)

-- | given an initial rule, run a single step and return all the (potentially
--   new) rule.
runRule :: forall m. (BSMC m)
  => RuleMeta -> RuleIB m () -> BSM m [(RuleMeta, RuleIB m ())]
runRule rm rule = do
  (rs, ns) <- getIntBindT $  runStateT (evalRule rule) rm
  pure $ map (\ a -> (ns, a)) rs

-- TODO :: Okay, the issue is that we are not properly preserving the full,
--        executable monad on lookup or anything, eval rule in particular ends
--        up discarding a bunch of .

-- | History aware lookup of rules.
insertRule :: forall m. (BSMC m) => RuleMeta -> RuleIB m () -> BSM m RuleID
insertRule rm@(RuleMeta hist watch _) rule = do
  lookupRuleHistory hist >>= \case
    Just rid -> pure rid
    Nothing  -> do
      rid <- newIdent
      traceShowM ('i', rid, hist)
      -- let mTarget = case rule of
      --       (RLook t v k) -> Just $ TID t (forceTID v)
      --       _ -> Nothing
      rules . at rid .= Just (Waiting (typeRep @(IntBindT m)) rm rule)
      for (HS.toList watch) (\ t -> do
        t' <- getRepExID t
        (RID rid) `dependsOn` t')
      hist' <- freshenHist hist
      traceShowM =<< (('1',) <$> use ruleHistories)
      ruleHistories %= HM.unionWith mergeRuleHistories (makeRuleHists rid hist')
      traceShowM =<< (('2',) <$> use ruleHistories)
      pure rid

  where

    makeRuleHists :: RuleID -> RuleHistory -> HashMap RuleID RuleHistories
    makeRuleHists rid (RuleHistory fam steps) = HM.singleton fam (makeFromSteps rid steps)

    makeFromSteps :: RuleID -> [ExID] -> RuleHistories
    makeFromSteps rid [] = RuleHistories (Just rid) mempty
    makeFromSteps rid (u:us) = RuleHistories Nothing (HM.singleton u $ makeFromSteps rid us)

    mergeRuleHistories :: RuleHistories -> RuleHistories -> RuleHistories
    mergeRuleHistories (RuleHistories f m) (RuleHistories f' m') =
      RuleHistories (f' <|> f) (HM.unionWith mergeRuleHistories m m')

freshenHist :: forall m. (BSMC m) => RuleHistory -> BSM m RuleHistory
freshenHist (RuleHistory fam stps) = RuleHistory fam <$> traverse getRepExID stps

getRepExID :: forall m. (BSMC m) => ExID -> BSM m ExID
getRepExID (RID r) = RID <$> getRuleRep r
getRepExID (TID tt t) = TID tt <$> getRepresentative t

lookupRule :: forall m. (BSMC m) => RuleID -> BSM m (Maybe (RuleMeta, RuleIB m ()))
lookupRule r = do
  r' <- getRuleRep r
  traceM $ "looking up: " <> show r <> " -- " <> show r'
  use (rules . at r') >>= \case
    Nothing -> panic "unreachable"
    Just (Merged _) -> panic "unreachable"
    Just (Waiting tm rm rule) -> pure $ do
      HRefl <- eqTypeRep tm (typeRep @(IntBindT m))
      pure (rm, rule)

lookupRuleHistory :: forall m. (BSMC m) => RuleHistory -> BSM m (Maybe RuleID)
lookupRuleHistory rh@(RuleHistory fam _)
  = do
    traceM $ "rh lookup: " <> show rh
    hist' <- freshenHist rh
    (>>= (lookupSteps $ hist' ^. nextStep)) <$> use (ruleHistories . at fam)

  where

    lookupSteps :: [ExID] -> RuleHistories -> Maybe RuleID
    lookupSteps [] (RuleHistories m _) = m
    lookupSteps (e:es) (RuleHistories _ hm)
      = HM.lookup e hm >>= lookupSteps es

getRuleRep :: forall m. (BSMC m) => RuleID -> BSM m RuleID
getRuleRep r = use (rules . at r) >>= \case
  Nothing -> panic "unreachable"
  Just (Merged r') -> do
    r'' <- getRuleRep r'
    rules . at r .= Just (Merged r'')
    pure r''
  Just _ -> pure r

-- | Lookup and run the relevant rule, insert the resulting next steps
triggerRule :: forall m. (BSMC m) => RuleID -> BSM m ()
triggerRule rid = lookupRule rid >>= \case
  Nothing -> panic "unreachable"
  Just rs -> traceShow ('t', rid) $ do
    traceShowM =<< (('t','r',) <$> use ruleHistories)
    results <- uncurry runRule rs
    traverse_ (triggerRule <=< uncurry insertRule) results

-- | adds a term to the watchlist and the history
addToWatched :: forall m t. (BSMTC m t) => TermID t -> RTIB m ()
addToWatched t = do
  watched %= HS.insert (toExID t)
  history . nextStep %= (<> [toExID t])
