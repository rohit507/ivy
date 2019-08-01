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


instance (MonadBind e (IntBindT m) t, BSEMTC e m t) => MonadUnify e (IntBindT m) t where

  equals = undefined
  unify = undefined
  subsume = undefined

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

instance Functor m => Functor (RuleT m) where
  fmap = undefined

instance (Monad m) => Applicative (RuleT m) where
  pure = undefined
  (<*>) = ap

-- | Yeah, no idea if this will work, the broad idea is we can compress
--   actions in m into RRun which we can execute, and the rest of the operations
--   can stay indivisible.
instance (Monad m) => Monad (RuleT m) where
  (>>=) = undefined

instance (MonadError e m) => MonadError e (RuleT m) where
  throwError = undefined

instance (MonadBind e m t
         , Hashable (Var m t)
         , Eq (Var m t)
         )
  => MonadBind e (RuleT m) t where

  type Var (RuleT m) = Var m

  freeVar = undefined
  bindVar = undefined
  lookupVar = undefined
  redirectVar = undefined

instance (MonadUnify e m t) => MonadUnify e (RuleT m) t where

  equals = undefined
  unify = undefined
  subsume = undefined

instance (MonadAssume e m t) => MonadAssume e (RuleT m) t

instance (MonadProperty e p m) => MonadProperty e p (RuleT m) where

instance (MonadError e m)
  => MonadRule e (IntBindT m) where
  type Rule (IntBindT m) = RuleT (IntBindT m)
  addRule = undefined

instance (MonadError e m) => MonadRule e (RuleT m) where
  type Rule (RuleT m) = RuleT m
  addRule = id

-- | Decompose a rule into a list of actions we can run to get the
--   next step in the rule.
execRule :: forall a m. (BSMC m) => RuleIB m a -> [RTIB m (RuleIB m a)]
execRule (RLook t v k) = pure $ do
  let v' = forceVID @(IntBindT m) v
  addToWatched v
  addToHistory Lookup v
  m <- k =<< (map (map forceTID) <$> (lift $ lookupVar v'))
  pure $ pure m

execRule (RBind t v g k) = pure $ do
  addToModified v
  addToHistory Bind v
  term <- g v
  new <- lift $ bindVar (forceVID v) (forceVID @(IntBindT m) <$> term)
  res <- k (forceTID new)
  pure $ pure res

execRule (RRun as) = map (map _) as



-- | Run action

-- I need to double check this entire instance for logic errors.
-- In particular how assumptions interact with rules and cyclicality.
--
-- There can be many rule closures instantiated as a single rule traverses the
-- tree in some fashion, and what if that rule ends up backtracking?
-- Is a historical log a sufficient identifier that we can use it
-- to prevent needless creation of new rules as they backtrack over
-- old ones?
--
-- Alternately, the better idea is probably to nullify an operation as soon as
-- it hits an assumption or a member of its visited set.
-- Since that would imply a cycle has been hit, and any further changes will
-- just happen as the cleaning operations repeatedly trigger on the lowest
-- level.
--
-- if I try to do this as a free monad, it'll require developing a proper
-- binding function, especially given that it'll need to hoist operations


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



-- | Adds rule to the rule set, using the history map to deconflict operations
--   as needed
insertRule :: RuleMeta -> RuleIB m () -> m RuleID
insertRule = undefined
  -- check if slug in history tree
  -- if yes then return that id
  -- otherwise
     -- get new RuleID
     -- insert into rule map
     -- insert into history map
     -- add the various dependencies.
     -- return new is


addToWatched :: TermID t -> RTIB m ()
addToWatched = undefined

addToModified :: TermID t -> RTIB m ()
addToModified = undefined

addToHistory :: (Newtype n Int) => RuleAction -> n -> RTIB m ()
addToHistory = undefined


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
