
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
import Ivy.Wrappers.IDs


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

-- | a getter for typed config data
toConfig :: forall m. (Typeable m) => Getting (Maybe (Config m)) Context (Maybe (Config m))
toConfig = to (\ (Context tm c _) -> eqTypeRep tm (typeRep @m) >>= (\ HRefl -> pure c))

-- | Generate a new internal identifier of some type.
--
--   First type parameter is the output ident type.
newIdent :: forall i m e. (IBM e m , Newtype i Int) => IBRWST m i
newIdent = (view $ toConfig @m) >>= \case
  Nothing -> panic "invalid Ident Type"
  Just conf -> pack <$> lift (conf ^. generateNewID)

-- | Creates a new free variable. w/ all associated bookkeeping
freeVarT :: forall t m e. (IBTM' e t m) => IBRWST m (TermID t)
freeVarT = do
  v :: TermID t <- newIdent
  setTermData v (Bound typeRep (typeRep @e) $ freeBoundState @t)
  applyDefaultRules v
  addToDepGraph (TID $ typedTID @t @e v)
  markDirty v
  pure v

-- | Looks up a variable after ensuring that it's been cleaned and updated.
lookupVarT :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m (Maybe (t (TermID t)))
lookupVarT t = do
  t' :: TermID t <- getRepresentative t
  cleanTerm t'
  let et' = typedTID @t @e t'
  (use $ termData . at @(HashMap TypedVar TermState) et') >>= \case
    Nothing -> panic " -- throwNonexistentTerm (unpackVID @_ t')"
    Just Forwarded{} -> panic " -- throwExpectedBoundState "
    Just (Bound tt te bs) -> matchType2 @t @e
      tt (throwInvalidTypeFound tt (typeRep @t))
      te (throwInvalidTypeFound te (typeRep @e))
      (\ HRefl HRefl -> pure $ bs ^. termValue)

freshenTerm :: forall t m e. (IBTM' e t m) => t (TermID t) -> IBRWST m (t (TermID t))
freshenTerm = traverse getRepresentative

bindVarT :: forall t m e. (IBTM' e t m) => TermID t -> t (TermID t) -> IBRWST m (TermID t)
bindVarT v t = do
  v'  <- getRepresentative v
  mot <- lookupVarT v'
  nt  <- freshenTerm t
  whenJust mot $ \ ot -> do
    let otd = getTermDeps ot
        ntd = getTermDeps nt
        tv' = TID $ typedTID @t @e v'
        lostDeps = HS.difference otd ntd
        newDeps  = HS.difference ntd otd
    unless (HS.null lostDeps) $ do
      traverse_ (removeDependency @m @e tv') $ HS.toList lostDeps
      markDirty v'
    unless (HS.null newDeps) $ do
      traverse_ (addDependency    @m @e tv') $ HS.toList newDeps
      markDirty v'
  setTermValue v' nt
  pure v'

-- | forwards the first term to the second, performs what additional bookkeeping
--   is needed. Returns the freshest new term.
forwardVarT :: forall t m e. (IBTM' e t m) => TermID t -> TermID t -> IBRWST m (TermID t)
forwardVarT old new = do
  o' <- getRepresentative old
  n' <- getRepresentative new
  when (o' /= n') $ do
    let to' = TID $ typedTID @t @e o'
        tn' = TID $ typedTID @t @e n'
    -- Move depends from old to new
    dependencies <- getDependencies o'
    traverse_ (manageDependencies to' tn') dependencies
    dependents <- getDependents o'
    traverse_ (manageDependents to' tn') dependents
    -- forward subsumptions as needed
    subsumed <- getSubsumedTerms o'
    traverse_ (subsumeT n') subsumed
    -- forward relations as needed
    forwardRelations o' n'
    updateRuleHistories o' n'
    addDependency tn' to'
  getRepresentative n'

  where

    manageDependencies old new dep = do
      removeDependency dep old
      addDependency    dep new

    manageDependents old new dep = do
      removeDependency old dep
      addDependency    new dep

type TheseVars t = These (TermID t) (TermID t)

-- | A generalized recursive binary operation that we can use to implement
--   equalsT, unionT, and the like.
recBinOpT :: forall a b t m e. (IBTM' e t m)
          => (TheseVars t -> IBRWST m (Maybe a))
          -- ^ check: short circuits op unless Nothing is returned
          -> (TheseVars t -> IBRWST m (Maybe b) -> IBRWST m (Maybe b))
          -- ^ assume: assumption to apply when recursing into child
          -> (e -> IBRWST m b)
          -- ^ handle: handle errors during a join
          -> (t a -> IBRWST m b)
          -- ^ collapse: collapse a term into a useful result
          -> (TheseVars t -> Maybe b -> IBRWST m a)
          -- ^ merge: final op on input terms
          -> TheseVars t
          -- ^ inputs: The input terms.
          -> IBRWST m a
recBinOpT check assume handle collapse merge inputs = do
  reps <- bitraverseThese getRepresentative getRepresentative inputs
  recBinOpG lookupVarT check assume handle collapse merge inputs

-- | A recursive binary op even further generalized to the point that
--   every major operation is pulled from an input
recBinOpG :: forall v a b t m e. (Monad m, Traversable t, JoinSemiLattice1 e t)
          => (v -> m (Maybe (t v)))
          -> (These v v -> m (Maybe a))
          -> (These v v -> m (Maybe b) -> m (Maybe b))
          -> (e -> m b)
          -> (t a -> m b)
          -> (These v v -> Maybe b -> m a)
          -> These v v
          -> m a
recBinOpG lookup check assume handle collapse merge inputs = do
  flip maybeM (check inputs) $ do
    subterm :: Maybe b <- assume inputs $
      bitraverseThese lookup lookup inputs >>= \case
        --
        This Nothing   -> nothingCase
        This (Just ta) -> thisCase ta
        --
        That Nothing   -> nothingCase
        That (Just tb) -> thatCase tb
        --
        These Nothing   Nothing   -> nothingCase
        These (Just ta) Nothing   -> thisCase ta
        These Nothing   (Just tb) -> thatCase tb
        These (Just ta) (Just tb) -> theseCase ta tb
    merge inputs subterm

  where

    recurse :: These v v -> m a
    recurse = recBinOpG lookup check assume handle collapse merge

    nothingCase = pure Nothing
    thisCase ta = Just <$> (collapse =<< (for ta $ recurse . This))
    thatCase tb = Just <$> (collapse =<< (for tb $ recurse . That))
    theseCase ta tb = Just <$> case liftLatJoin ta tb of
      Left e -> handle e
      Right tu -> collapse =<< for tu recurse

-- | a list of operations to perform
type OpSet = HashSet (TypedVar, TypedVar)
type UnificationSet = OpSet
type SubsumptionSet = OpSet

-- | Returns nothing if the terms aren't equal, otherwise it returns a list
--   of terms that should be unified to unify the input terms.
equalsT :: forall t m e. (IBTM' e t m)
   => TermID t -> TermID t -> IBRWST m (Maybe UnificationSet)
equalsT a b = recBinOpT check assume handle collapse merge (These a b)

  where
    check (These a b) =
      ifM (pure (a == b) ||^ isAssumedEqual a b ||^ isAssumedUnified a b)
          (pure . Just $ Just mempty) (pure Nothing)
    check _ = pure . Just $ Just mempty

    assume (These a b) = withAssumption @_ @_ @e (isEqualTo @t @e a b)
    assume _ = id

    handle _ = pure $ Nothing

    collapse :: t (Maybe OpSet) -> IBRWST m (Maybe OpSet)
    collapse term = pure $ foldr mappendMaybe (Just mempty) term


    ta = typedTID @t @e a
    tb = typedTID @t @e b

    merge :: TheseVars t -> Maybe (Maybe OpSet) -> IBRWST m (Maybe OpSet)
    merge (This _) meq = pure $ join meq
    merge (That _) meq = pure $ join meq
    merge (These _ _) meq = do
      let eqs = mappendMaybe (Just $ HS.singleton (ta,tb)) (join meq)
      (`mappendMaybe` eqs) <$> equalsPropsT a b


-- | unifies all the various terms as needed.
unifyT :: forall t m e. (IBTM' e t m) => TermID t -> TermID t -> IBRWST m (TermID t)
unifyT a b = recBinOpT check assume handle collapse merge (These a b)
  where

    check (This a) = pure $ Just a
    check (That b) = pure $ Just b
    check (These a b) = ifM (pure (a == b) ||^ isAssumedUnified a b)
      (pure $ Just b) (pure $ Nothing)

    assume (These a b) = withAssumption (isEqualTo @t @e a b)
    assume _ = panic "invariant broken: check skips any non-These inputs"

    handle = throwError

    collapse = pure

    merge (These a b) mTerm = do
      unifyPropsT a b
      forwardVarT a =<< maybe (pure b) (bindVarT b) mTerm
    merge _ _ = panic "invariant broken: check skips any non-These inputs"

-- | Asserts that the first term subsumes the second. Returns the second term.
subsumeT :: forall t m e. (IBTM' e t m) => TermID t -> TermID t -> IBRWST m (TermID t)
subsumeT a b = recBinOpT check assume handle collapse merge (These a b)
  where

    -- if we've only got the subsumed side of the term then we should create
    -- a free variable that can be any greater value.
    check (This a) = Just <$> (subsumeT a =<< freeVarT)
    check (That b) = pure $ Just b
    check (These a b) =
      ifM (pure (a == b) ||^ inSubsumeSet a b
            ||^ isAssumedUnified a b ||^ isAssumedSubsumed a b )
          (pure $ Just b)
          -- If b <= a and a <= b then a == b
          (ifM (inSubsumeSet b a) (Just <$> unifyT a b) (pure Nothing))

    assume (These a b) = withAssumption (isSubsumedBy @t @e a b)
    assume _ = panic "invariant broken: check skips any non-These inputs"

    handle = throwError

    collapse = pure

    merge (These a b) mTerm
      = addToSubsumeSet a =<< maybe (pure b) (bindVarT b) mTerm

-- | Checks all the properties of each input term and returns those that
--   need to be unified.
equalsPropsT :: forall t m e. (IBTM' e t m)
   => TermID t -> TermID t -> IBRWST m (Maybe UnificationSet)
equalsPropsT a b = do
  pma <- getPropMap a
  pmb <- getPropMap b
  let intersectionMap :: TypeMap (OfType ())
        = TM.intersection (TM.map empty pma) pmb
  sets :: TypeMap (OfType (Maybe OpSet)) <- TM.traverse (getOp pma pmb) intersectionMap
  pure $ foldr mappendMaybe (Just mempty) (TM.toList sets)

  where

    empty :: forall t a. (Typeable t)
       => Proxy t -> a -> ()
    empty _ _ = ()

    getOp :: forall (g :: Type). (Typeable g)
          => TypeMap PropMap
          -> TypeMap PropMap
          -> Proxy g
          -> ()
          -> IBRWST m (Maybe OpSet)
    getOp rma rmb p _ = map join . sequenceA $ do
      (TVar tta tea ta) <- TM.lookup @g @PropMap typeRep rma
      (TVar ttb teb tb) <- TM.lookup @g @PropMap typeRep rmb
      HRefl <- eqTypeRep tta ttb
      HRefl <- eqTypeRep tea teb
      HRefl <- eqTypeRep tea (typeRep @e)
      Just $ equalsT @_ @m @e ta tb

-- | Since each property is a function we need to ensure that the
--   properties of unified terms are themselves unified.
unifyPropsT :: forall t m e. (IBTM' e t m)
   => TermID t -> TermID t -> IBRWST m ()
unifyPropsT a b = do
  pma <- getPropMap a
  pmb <- getPropMap b
  let intersectionMap :: TypeMap (OfType ())
        = TM.intersection (TM.map empty pma) pmb
  _ :: TypeMap (OfType ()) <- TM.traverse (unifyOp pma pmb) intersectionMap
  skip

  where

    empty :: forall t a. (Typeable t)
       => Proxy t -> a -> ()
    empty _ _ = ()

    unifyOp :: forall (g :: Type). (Typeable g)
          => TypeMap PropMap
          -> TypeMap PropMap
          -> Proxy g
          -> ()
          -> IBRWST m ()
    unifyOp rma rmb p _ = fromMaybe (panic "unreachable") $ do
      (TVar tta tea ta) <- TM.lookup @g @PropMap typeRep rma
      (TVar ttb teb tb) <- TM.lookup @g @PropMap typeRep rmb
      HRefl <- eqTypeRep tta ttb
      HRefl <- eqTypeRep tea teb
      HRefl <- eqTypeRep tea (typeRep @e)
      Just $ unifyT @_ @m @e ta tb *> skip

-- | Gets a property of p, if said property does not exist, then creates a
--   free Variable for it.
propertyOfT :: forall p t t' m e. (Property p t t', IBTM' e t m, IBTM' e t' m)
  => p -> TermID t -> IBRWST m (TermID t')
propertyOfT p t = do
  pm <- getPropMap =<< getRepresentative t
  case (TM.lookup (typeRep @p) pm) of
    Just (TVar tt te t) -> matchType2 @t' @e
      tt (throwInvalidTypeFound tt (typeRep @t'))
      te (throwInvalidTypeFound te (typeRep @e ))
      (\ HRefl HRefl -> pure t)
    Nothing -> do
      t' :: TermID t' <- freeVarT
      addProp p t t'
      pure t'

addGeneralRuleT :: forall t m e. (IBTM' e t m)
  => (VarIB t m -> Rule (IntBindT m) ()) -> IBRWST m ()
addGeneralRuleT rule = do
  rid <- newIdent
  addToDefaultRules rid (rule . unpackVID)
  traverse_ (addSpecializedRuleT rid . rule . unpackVID) =<< getAllTerms @t

-- | This adds a new rule with a new historical identifier to the map
addSpecializedRuleT :: forall m e. (IBM' e m)
  => RuleID -> Rule (IntBindT m) () -> IBRWST m ()
addSpecializedRuleT initial = runRule (RuleHistory initial [])

-- | This will execute a rule and then add the rule to the graph as needed.
--   Performs all the additionall bookkeeping.
runRule :: forall m e. (IBM' e m)
  => RuleHistory -> Rule (IntBindT m) () -> IBRWST m ()
runRule = undefined

-- | Runs a rule up to the point where it performs some manipulation of the
--   term graph, whether that is a read or a write operation.
execRule :: forall m e. (IBM' e m)
  => Rule (IntBindT m) () -> IBRWST m [Rule (IntBindT m) ()]
execRule = undefined

forwardRuleT :: RuleID -> RuleID -> IBRWST m RuleID
forwardRuleT old new = undefined

-- | This will go on forever if your rules don rules don't settle down
cleanTerm :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m ()
cleanTerm t = (view $ toConfig @m) >>= \case
  Nothing -> panic "invalid config"
  Just c  -> go 0 t (c ^. maxCyclicUnifications)

  where

    go :: Int -> TermID t -> Int -> IBRWST m ()
    go n t maxi = do
      when (n > maxi) $ panic "Cycle didn't quiesce in time"
      t' <- getRepresentative t
      if (t /= t')
        then (withAssumption (assumeClean @t @e t) $ cleanTerm t') *> markClean t
        else whenM (isDirty t') $ do
          _ <- withAssumption (assumeClean @t @e t') $ do
            -- We mark the term as clean here, so that any changes to the term
            -- will dirty it. Keep in mind that marking a term as dirty or clean
            -- does not pay ant attention to assumptions
            markClean t'
            cleanDependencies t'
            applySubsumptions t'
            runRuleDependencies t'
          go (n + 1) t' maxi

-- | Applies a forwarded term to the rule history map, and prunes the rule list
--   as needed.
updateRuleHistories :: forall t m e. (IBTM' e t m)
  => TermID t -> TermID t -> IBRWST m ()
updateRuleHistories = undefined

forwardRelations :: forall t m e. (IBTM' e t m)
  => TermID t -> TermID t -> IBRWST m ()
forwardRelations = undefined

getSubsumedTerms :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m (HashSet (TermID t))
getSubsumedTerms = undefined


-- | Just sets the term value, doesn't do any bookkeeping
setTermValue :: forall t m e. (IBTM' e t m)
             => TermID t -> t (TermID t) -> IBRWST m ()
setTermValue = undefined

-- | Runs through the entire
getTermDeps :: t (TermID t) -> HashSet InternalID
getTermDeps = undefined

type Dependency = InternalID
type Dependent = InternalID

-- | removes a dependency from the dependency graph, errors if the
--   dependency does not exist.
removeDependency :: forall m e. (IBM' e m)
               => Dependency -> Dependent -> IBRWST m ()
removeDependency _dependent _depender = undefined

addDependency :: forall m e. (IBM' e m)
             => Dependency -> Dependent -> IBRWST m ()
addDependency _ _to = undefined

getBoundData :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m (BoundState t)
getBoundData = undefined

setTermData :: forall t m e. (IBTM' e t m)
            => TermID t -> TermState -> IBRWST m ()
setTermData i s = termData . at (typedTID @t @e i) .= Just s

applyDefaultRules :: forall t m e. (IBTM' e t m)
                  => TermID t -> IBRWST m ()
applyDefaultRules = undefined

addToDepGraph :: InternalID -> IBRWST m ()
addToDepGraph = undefined


isDirty :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m Bool
isDirty (typedTID @t @e -> t)
  =  (not <$> isAssumedClean  @t @m @e t)
  ||^ (HS.member t <$> use dirtySet)

isAssumedClean :: forall t m e. (IBTM' e t m) => TypedVar -> IBRWST m Bool
isAssumedClean t = do
  let cleanAssumption = buildAssuming $ IsClean t
  result <- assumingIntersects cleanAssumption . _assumptions <$> ask
  when result $ tell cleanAssumption
  pure result

-- | Runs the child computation with some assumption held as true.
withAssumption :: forall a m e. (IBM' e m) => Assumption -> IBRWST m a -> IBRWST m a
withAssumption (buildAssuming -> added) act =
   local modifyAssumptions act


  where

    modifyAssumptions b@Context{..} = b{_assumptions=_assumptions <> added}


-- | is the second element in the subsumtion set of the first
inSubsumeSet :: forall t m e. (IBTM' e t m)
  => TermID t -> TermID t -> IBRWST m Bool
inSubsumeSet = undefined

-- | add the second element to the subsume set of the first. Also adds
--   a dependency to the graph.
addToSubsumeSet :: forall t m e. (IBTM' e t m)
  => TermID t -> TermID t -> IBRWST m (TermID t)
addToSubsumeSet = undefined

getDependencies :: forall t m e. () => TermID t -> IBRWST m (HashSet InternalID)
getDependencies = undefined

getDependents :: forall t m e. () => TermID t -> IBRWST m (HashSet InternalID)
getDependents = undefined

applySubsumptions :: forall t m e. () => TermID t -> IBRWST m ()
applySubsumptions = undefined

cleanDependencies :: forall t m e. () => TermID t -> IBRWST m ()
cleanDependencies = undefined

runRuleDependencies :: forall t m e. () => TermID t -> IBRWST m ()
runRuleDependencies = undefined

-- | Flags all child terms as dirty as well, stepping through what rules
--   can modify this term.
markDirty :: forall t m e. () => TermID t -> IBRWST m ()
markDirty = undefined

markClean :: forall t m e. () => TermID t -> IBRWST m ()
markClean = undefined

getRepresentative :: forall t m e. () => TermID t -> IBRWST m (TermID t)
getRepresentative = undefined

isAssumedEqual :: forall t m e. (IBTM' e t m) => TermID t -> TermID t -> IBRWST m Bool
isAssumedEqual = undefined

isAssumedSubsumed :: forall t m e. (IBTM' e t m) => TermID t -> TermID t -> IBRWST m Bool
isAssumedSubsumed = undefined

isAssumedUnified :: forall t m e. (IBTM' e t m) => TermID t -> TermID t -> IBRWST m Bool
isAssumedUnified = undefined

getPropMap :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m (TypeMap PropMap)
getPropMap = undefined

addProp :: forall p t t' m e. (Property p t t', IBTM' e t m, IBTM' e t' m)
  => p -> TermID t -> TermID t' -> IBRWST m ()
addProp = undefined

addToDefaultRules :: forall t m e. (IBTM' e t m)
  => RuleID -> (TermID t -> Rule (IntBindT m) ()) -> IBRWST m ()
addToDefaultRules = undefined

getAllTerms :: forall t m e. (IBTM' e t m)
  => IBRWST m [TermID t]
getAllTerms = undefined

type VarIB t m = Var t (IntBindT m)

instance (IBTM' e t m) => MonadBind t (IntBindT m) where

  type Var t = VarID t

{-
  freeVar :: IntBindT m (VarIB t m)
  freeVar = IntBindT $ unpackVID @(IntBindT m) <$> freeVarT

  lookupVar :: VarIB t m -> IntBindT m (Maybe (t (VarIB t m)))
  lookupVar
    = IntBindT . ( _ $ unpackVID @t @(IntBindT m))
    . lookupVarT . crushVID

  bindVar :: VarIB t m -> t (VarIB t m) -> IntBindT m (VarIB t m)
  bindVar v t = IntBindT $ unpackVID @(IntBindT m) <$> bindVarT (crushVID v) (crushVID <$> t)


-- | Create a free var in IBRWST
freeVarT ::forall t m e. (IBTM' e t m) => IBRWST m (TermID t)
freeVarT = do
  i <- newIdent @(TermID t)
  setTermState i $ freeTermState i
  pure i

-- | When looking up a variable we need to find its representative.
lookupVarT :: forall t m e. (IBTM' e t m)
           => TermID t m -> IBRWST m (Maybe (t (TermID t m)))
lookupVarT v = do
  v' <- getRepresentative v
  termValue <$> getBoundState v'

-- | Binds a variable to a term, performs additional bookkeeping
--
--   TODO :: Bookkeeping?
--    - Update dependencies, potentially marl
bindVarT :: forall t m e. (IBTM' e t m)
         => TermID t m -> t (TermID t m) -> IBRWST m (TermID t m)
bindVarT v t = do
    v' <- getRepresentative v
    modifyBoundState v' (pure . modif)
    pure v'
  where
    modif s@BoundState{..} = s{termValue = Just t}




-- | Ensures that the type of the term state matches the type of the
--   input variable.
validateTermStateType :: forall t m e. (IBTM' e t m)
                      => TermID t m -> TermState -> IBRWST m ()
validateTermStateType _ st = case st of
  (Bound     trt tre _) -> validateTypes trt trm
  (Forwarded trt tre _) -> validateTypes trt trm

  where

    validateTypes :: (Typeable t', Typeable m')
                  => TypeRep t'
                  -> TypeRep m'
                  -> IBRWST m () -- (t :~~: t', m :~~: m`)
    validateTypes tt tm  = do
      matchType @t
         tt (throwInvalidTypeFound tt (typeRep @t))
         (const skip)
      matchType @(IntBindT m)
         tm (throwInvalidTypeFound tm (typeRep @(IntBindT m)))
         (const skip)

-- | Gets the TermState for a variable, without further traversing
--   the network of connections to get to the final element.
getTermState :: (IBTM' e t m) => TermID t m -> IBRWST m TermState
getTermState v = whileGettingTermStateOf v $ do
  td <- termData <$> get
  case IM.lookup (flattenVID v) td of
    Nothing -> throwNonexistentTerm v
    Just ts -> validateTermStateType v ts *> pure ts

-- | Sets the termState for a variable without additional bookkeeping.
--
--   FIXME :: If termState is an error, and the thing to be inserted is an error
--      merge the errors, otherwise trying to set an errored term should be
--      a nop
setTermState :: (IBTM' e t m) => TermID t m -> TermState -> IBRWST m ()
setTermState var term = whileSettingTermStateOf var $ do
  validateTermStateType var term
  modify (\ b -> b{termData = IM.insert (flattenVID var) term $ termData b})

-- | Modifies the term state of something with a function, does not
--   do additional bookkeeping.
modifyTermState :: (IBTM' e t m)
                => TermID t m
                -> (TermState -> IBRWST m TermState)
                -> IBRWST m ()
modifyTermState v f = getTermState v >>= f >>= setTermState v


-- | Potentially gets a BoundState for a variable throwing an error if the
--   type is incorrect. Does not traverse to find the final element.
getBoundState :: forall t m e. (IBTM' e t m) => TermID t m -> IBRWST m (BoundStateIB t m)
getBoundState v = getTermState v >>= \case
  (Bound tt tm bs) -> matchType2 @t @(IntBindT m)
     tt (throwInvalidTypeFound tt (typeRep @t))
     tm (throwInvalidTypeFound tm (typeRep @(IntBindT m)))
     (\ HRefl HRefl -> pure bs)
  _ -> throwExpectedBoundState v

-- | Sets the boundState of a trm

setBoundState :: forall t m e. (IBTM' e t m) => TermID t m -> BoundStateIB t m -> IBRWST m ()
setBoundState v n = modifyBoundState v (\ _ -> pure n)

-- | Modifies the bound state of a term, automatically dirties term if
--   there's a change.
modifyBoundState :: forall t m e. (IBTM' e t m)
                 => TermID t m
                 -> (BoundStateIB t m -> IBRWST m (BoundStateIB t m))
                 -> IBRWST m ()
modifyBoundState v f = do
  bs <- getBoundState v
  bs' <- f bs
  whenM (isBoundStateUpdated bs bs')
    $ setTermState v (Bound typeRep typeRep bs'{dirty=True})

-- | Checks whether two bound states are semantically different
--
--   TODO :: Make the check more thorough rather than only checking term equality.
isBoundStateUpdated :: forall t m e. (IBTM' e t m)
                    => BoundStateIB t m
                    -> BoundStateIB t m
                    -> IBRWST m Bool
isBoundStateUpdated old new = case (termValue old, termValue new) of
  (Nothing, Nothing) -> pure False
  (Just otv, Just ntv) -> isJust <$> equalizeTerms @t @m @e otv ntv
  (Just _, Nothing) -> throwInvalidTermUpdate "Updating a Bound term to Free."
  _ -> pure True

-- | Potentially gets a forwarded var for a variable throwing an error if the
--   type is incorrect. Does not traverse to find the final element.
getForwardingVar :: forall t m e. (IBTM' e t m) => TermID t m -> IBRWST m (Maybe (TermID t m))
getForwardingVar v = getTermState v >>= \case
  (Forwarded tt tm i) -> matchType2 @t @m
     tt (throwInvalidTypeFound tt (typeRep @t))
     tm (throwInvalidTypeFound tm (typeRep @m))
     (\ HRefl HRefl -> pure $ Just i)
  _ -> pure Nothing


--  | Tries to get the error corresponding to a particular term.
--   Does not try to traverse the forwarding chain.
-- getTermError :: forall t m e. (IBTM' e t m) => TermID t m -> IBRWST m (Maybe e)
-- getTermError v = getTermState v >>= \case
--  (Errored _ _ te i) -> matchType @e
--     te (throwInvalidTypeFound te (typeRep @e))
--     (\ HRefl -> pure $ Just i)
--  _ -> pure Nothing

-- | Finds the Representative element for a Var in our disjoint set structure.
--
--   Element returned should always be an Error or a Bound Term.
--   Forwards paths as needed.
getRepresentative :: forall t m e. (IBTM' e t m) => TermID t m -> IBRWST m (TermID t m)
getRepresentative v = whileGettingRepresentativeOf v $ getForwardingVar v >>= \case
  Nothing -> pure v
  Just v' -> do
    v'' <- getRepresentative v'
    when (v' /= v'') $ setTermState v (Forwarded typeRep typeRep v'')
    pure v''

instance (forall e. IBTM' e t m, Show (t (TermID t m))) => MonadUnify t (IntBindT m) where

  unify :: TermID t m -> TermID t m -> IntBindT m (TermID t m)
  unify a b = IntBindT $ unifyT a b

  -- equals :: TermID t m -> TermID t m -> IntBindT m Bool
  -- equals a b = IntBindT $ equalsT a b


-- | Unify two terms in IBRWST and return the resulting outcome.
unifyT :: forall t m e.  (IBTM' e t m)
       => TermID t m -> TermID t m -> IBRWST m (TermID t m)
unifyT a b
  | a == b = pure a
  | otherwise = whileUnifyingTerms a b $ do
      a' <- getRepresentative a
      b' <- getRepresentative b
      ifM (assumeUnified a' b') (pure b) $ -- Don't want to loop.
        if ((a /= a') || (b /= b'))
        then unifyT a' b'
        else do
          mtva <- termValue <$> getBoundState a'
          mtvb <- termValue <$> getBoundState b'
          case (mtva, mtvb) of
            (Just tva, Just tvb) -> do
               eetv <- map fst $ withAssumption (a' `isUnifiedWith` b') $
                                   liftLatJoin @e pure pure unifyT tva tvb
               tv <- liftEither eetv
               modifyBoundState b' (\ s -> pure s{termValue=Just tv})
            _ -> skip -- At least one term is free, we don't need to do much here.

          unifyLevel a' b'

{-- | Check whether two terms are equivalent up to unification
equalsT :: (IBTM' e t m) => TermID t m -> TermID t m -> IBRWST m Bool
equalsT a b
  | a == b = pure True
  | otherwise = undefined
    -- Check if unification or requality assumed -}

-- | Unifies a single level of terms, with the assumption that they are both
--   representatives of their category, and that all their subterms are properly
--   unified.
unifyLevel :: (IBTM' e t m) => TermID t m -> TermID t m -> IBRWST m (TermID t m)
unifyLevel a b = do
  bsa <- getBoundState a
  modifyBoundState b (mergeBoundState a bsa)
  forwardTo a b

-- | Forwards the first var to the second, returns the second var.
forwardTo :: (IBTM' e t m) => TermID t m -> TermID t m -> IBRWST m (TermID t m)
forwardTo from to = do
  modifyTermState from (const . pure $ Forwarded typeRep typeRep to)
  pure to

-- | Getting the latest version of a term, by updating all its member variables.
freshenTerm :: forall t m e. (IBTM' e t m)
              => t (TermID t m)
              -> IBRWST m (t (TermID t m))
freshenTerm = traverse getRepresentative

-- | If terms are functionally identical, merge them into a new entry.
equalizeTerms :: forall t m e. (IBTM' e t m)
              => t (TermID t m)
              -> t (TermID t m)
              -> IBRWST m (Maybe (t (TermID t m)))
equalizeTerms ta tb = do
  ta' <- freshenTerm ta
  tb' <- freshenTerm tb
  pure $ if (not $ liftEq (==) ta' tb')
         then Just ta
         else Nothing

-- | Merge two bound states if possible. Can trigger unification of relations.
--   will verify that subterms are properly unified.
mergeBoundState :: forall e t m. (IBTM' e t m)
                => TermID t m -- ^ from
                -> BoundStateIB t m -- ^ from
                -> BoundStateIB t m -- ^ to
                -> IBRWST m (BoundStateIB t m)
mergeBoundState fromVar BoundState{termValue=ftv
                               , relations=fr
                               , forwardedFrom=ff
                               , subsumedTerms=fs
                               , ruleSet=frs
                               }
                BoundState{termValue=ttv
                             ,relations=tr
                             ,forwardedFrom=tf
                             ,subsumedTerms=ts
                             ,ruleSet=trs
                             }
  = BoundState <$> matchTerms ftv ttv
               <*> mergeRels tr
               <*> mergeForwarded ff tf
               <*> mergeSubsumed  fs ts
               <*> mergeRuleSet frs trs
               <*> pure True

  where

    matchTerms Nothing a = pure a
    matchTerms a Nothing = pure a
    matchTerms (Just ftv) (Just ttv) = equalizeTerms @t @m @e ftv ttv >>= \case
      Nothing ->  throwTermsNotUnified ftv ttv
      a -> pure a

    mergeRels :: TypeMap RelMap -> IBRWST m (TypeMap RelMap)
    mergeRels tr = TM.traverse mergeRelMap tr

    mergeRelMap :: forall p. (Typeable p) => Proxy p -> TypedVar -> IBRWST m TypedVar
    mergeRelMap proxy t@(TVar tt tm te tv) = case TM.lookup proxy fr of
      Nothing -> pure t
      Just (TVar ft fm fe fv) -> mergeTypedVars tt tm ft fm tv fv

    -- You know what, this entire thing is a bit absurd, ensuring that
    -- three sets of terms all properly match. oh well.
    mergeTypedVars ::forall ta ma tb mb e' e''.
                   (Typeable ta, Typeable ma, Typeable tb
                   ,Typeable mb, IBTM' e' ta ma, IBTM' e'' tb mb)
                   => TypeRep ta -> TypeRep ma
                   -> TypeRep tb -> TypeRep mb
                   -> TermID ta ma -> TermID tb mb -> IBRWST m TypedVar
    mergeTypedVars _ tma ttb tmb va vb = matchType2 @ta @ma
      ttb (throwInvalidTypeFound ttb (typeRep @ta))
      tmb (throwInvalidTypeFound tmb (typeRep @ma))
      (\ HRefl HRefl -> matchType2 @m @m
        tma (throwInvalidTypeFound tma (typeRep @m))
        tmb (throwInvalidTypeFound tma (typeRep @m))
        (\ HRefl HRefl -> matchType2 @e @e
          (typeRep @e') (throwInvalidTypeFound (typeRep @e') (typeRep @e))
          (typeRep @e'') (throwInvalidTypeFound (typeRep @e'') (typeRep @e))
          (\ HRefl HRefl -> TVar ttb (typeRep @m) (typeRep @e) <$> unifyT va vb )))


    mergeForwarded f t = pure $ f <> t <> IS.singleton fromVar

    mergeSubsumed f t = pure $ f <> t

    mergeRuleSet f t = do
      f' <- refreshRuleSet f
      t' <- refreshRuleSet t
      pure $ HM.union f' t'

-- | Run some computation while assuming some things, return the
--   result of that computation and which of the assumptions were triggered.
--
--   Returns the state of the assumption stack to what it was before the
--   action, so that we aren't accidentally keeping identifiers around that
--   shouldn't be.
--
--   This is really useful for dealing with large cyclic operations, by
--   keeping a more precise analogue of a visited set in a relatively
--   invisible way.
--
--   FIXME :: This entire enterprise is implemented in an incredibly slow
--           way. Do it better.
withAssumption :: Monad m => Assumption -> IBRWST m a -> IBRWST m (a,Bool)
withAssumption as act = do
   ((),w) <- listen skip
   local modifyAssumptions $ do
     (a,w') <- censor (const w) $ listen act
     tell $ assumingIntersection w w'
     pure (a, assumingIntersects w' addedAssumptions)

  where
    convert (IsEqualTo     a b) = mempty{equal=HS.fromList [(a,b),(b,a)]}
    convert (IsSubsumedBy  a b) = mempty{subsumed=HS.singleton (a,b)}
    convert (IsUnifiedWith a b) = mempty{unified=HS.fromList [(a,b),(b,a)]}

    addedAssumptions = convert as

    modifyAssumptions b@Context{..} = b{assumes=assumes <> addedAssumptions}


-- | Checks whether two terms are marked as having been unified in our
--   assumptions. If yes, then adds the corresponding unification term
--   to the read set and moves on.
assumeUnified :: Monad m => TermID t m -> TermID t m -> IBRWST m Bool
assumeUnified v v' = (||) <$> check v v' <*> check v' v

  where

    check i i' = do
      let pair = (flattenVID i, flattenVID i')
      res <- HS.member pair . unified . assumes <$> ask
      when res . tell $ mempty{unified=HS.singleton pair}
      pure res

-- | Checks whether we have an assumption of equality, if yes then
--   writes out the equality to the read set.
assumeEquals :: Monad m => TermID t m -> TermID t m -> IBRWST m Bool
assumeEquals v v' = (||) <$> check v v' <*> check v' v

  where

    check i i' = do
      let pair = (flattenVID i, flattenVID i')
      res <- HS.member pair . equal . assumes <$> ask
      when res . tell $ mempty{equal=HS.singleton pair}
      pure res

instance (forall e. IBTM' e t m, Show (t (TermID t m))) => MonadSubsume t (IntBindT m) where

  -- TODO :: Okay so the question is how do we properly recurse? do we
  --        filter step by step, or what.
  subsume :: TermID t m -> TermID t m -> IntBindT m ()
  subsume a b = IntBindT $ subsumeT a b *> skip

  -- subsumes :: TermID t m -> TermID t m -> IntBindT m Bool
  -- subsumes = undefined
    -- Check structuralEquality
    -- check equality and unity assumptions
    -- check subsume assumptions
    -- check layer by layer subsumption.
       -- TODO :: unclear how to do.

-- | This just subsumes one term to another on a one off basis.
--
--   TODO :: Clean this up, it's too imperative.
subsumeT :: forall t m e. (IBTM' e t m) => TermID t m -> TermID t m -> IBRWST m (TermID t m)
subsumeT a b
  | a == b = pure a
  | otherwise = whileSubsumingTerms a b $ do
     a' <- getRepresentative a
     b' <- getRepresentative b
     ifM (assumeSubsumed a' b' ||^ assumeUnified a' b') (pure b) $ -- Don't want to loop.
       if ((a /= a') || (b /= b'))
       then subsumeT a' b'
       else do
         ifM (b' `hasSubsumed` a) (unifyT a' b') $ do
           mtva <- termValue <$> getBoundState a'
           mtvb <- termValue <$> getBoundState b'
           case mtva of
             (Just tva) -> do
                tvb <- case mtvb of
                  Just tvb -> pure tvb
                  -- If the result term is free, then we can just fill the
                  -- current term with free variables.
                  Nothing -> traverse (\ _ -> freeVarT) tva
                eetv <- map fst $ withAssumption (a' `isSubsumedBy` b') $
                                    liftLatJoin @e pure pure subsumeT tva tvb
                tv <- liftEither eetv
                -- We only need to modify the subsumed term
                modifyBoundState b' (\ s -> pure s{termValue=Just tv})
             _ -> skip -- At least one term is free, we don't need to do much here.
           modifyBoundState a' (\ s@BoundState{subsumedTerms=subs} ->
                     pure s{subsumedTerms=subs <> IS.singleton b'})
           pure b'

-- | Checks whether one term is subsumed by another in our assumptions.
assumeSubsumed :: Monad m => TermID t m -> TermID t m -> IBRWST m Bool
assumeSubsumed v v' = do
  let pair = (flattenVID v, flattenVID v')
  res <- HS.member pair . subsumed . assumes <$> ask
  when res . tell $ mempty{subsumed=HS.singleton pair}
  pure res

-- | Checks whether a is marked as a subsumed term of b
hasSubsumed :: (IBTM' e t m) => TermID t m -> TermID t m -> IBRWST m Bool
hasSubsumed a b = do
  a' <- getRepresentative a
  b' :: TermID t m <- getRepresentative b
  tis <- subsumedTerms <$> getBoundState a'
  let tl = IS.toList tis
  tl' <- traverse getRepresentative tl
  let tl'' = IS.fromList tl'
  modifyBoundState a' (\ s -> pure s{subsumedTerms=tl''})
  pure $ IS.member b' tl''

instance (Property p t t', IBTM' e t m, IBTM' e t' m)
       => MonadProperty p t t' (IntBindT m) where

  propertyOf :: TermID t m -> IntBindT m (TermID t' m)
  propertyOf v = IntBindT . whileGettingPropertyOf v (typeRep @p) $ do
    v' :: TermID t m <- getRepresentative v
    tm :: TypeMap RelMap <- relations <$> getBoundState v'
    case TM.lookup (typeRep @p) tm of
      Nothing -> do
        nv :: TermID t' m <- freeVarT
        modifyBoundState v' (\ b@BoundState{relations=rl} ->
              pure b{relations= TM.insert (typeRep @p) (tVar nv) rl})
        pure nv
      Just (TVar tt tm _ nv) -> matchType2 @t' @m
        tt (throwInvalidTypeFound tt (typeRep @t'))
        tm (throwInvalidTypeFound tm (typeRep @m))
        (\ HRefl HRefl -> pure nv)

instance (MonadError e (IntBindT m), MonadAttempt m) => MonadAttempt (IntBindT m) where

  attempt :: IntBindT m (Either f b) -> (f -> IntBindT m b) -> IntBindT m b
  attempt = defaultErrorLiftAttempt
              (\ (a,s,w) -> (((),s,w),a))
              (\ (((),s,w), a) -> (a,s,w))

-- | Stuff that, for now we're just going to assume exists


instance (Monad m) => Monad (Rule m) where
  (Act m) >>= k = Run . map (:[]) $ k <$> m
  (Run m) >>= k = Run $ (map $ map (>>= k)) m
  (Watch w u) >>= k = Watch w $ map (map (>>= k)) u


refreshTVar :: forall m e. (IBM e m)
  => TypedVar -> IBRWST m TypedVar
refreshTVar (TVar tt tm te n) = matchType2 @m @e
  tm (throwInvalidTypeFound tm (typeRep @m))
  te (throwInvalidTypeFound tm (typeRep @m))
  (\ HRefl HRefl -> TVar tt tm te
    . unsafeExpandVID
    . unsafeExpandTID
    . flattenVID <$> getRepresentative @_ @m @e n)

refreshHistory :: (IBM e m) => History -> IBRWST m History
refreshHistory (History ident terms)
  = History ident <$> traverse refreshTVar terms

refreshRuleSet :: (IBM e m) => RuleSetIB m -> IBRWST m (RuleSet m)
refreshRuleSet hm
  = HM.fromList <$> traverse (\ (a,b) -> (,b) <$> refreshHistory a)
                            (HM.toList hm)

-- | Adds some rules to the thing.
addRules :: TermID t m -> RuleSetIB m -> IBRWST m ()
addRules v s = modifyBoundState v (\ b -> do
                 rs' <- refreshRuleSet $ ruleSet b
                 s' <- HM.filterWithKey
                    (\ k _ -> not $ HM.member k rs')
                    <$> refreshRuleSet s
                 if HM.null s'
                 then pure b
                 else pure b{ruleSet=HM.union s' rs', dirty=True})

runRules :: forall m. RuleSetIB m -> IBRWST m ()
runRules (HM.toList -> rl) = undefined

  where

    addTVRule :: (TypedVar, RuleSetIB m) -> IBRWST m ()
    addTVRule (TVar tt tm te v, rs) = addRules v rs

    collapseRuleList :: [(TypedVar, RuleSetIB m)] -> HashMap TypedVar (RuleSetIB m)
    collapseRuleList
      = foldr (\ (tv,rs) -> HM.adjust (\ rs' -> HM.union rs' rs) tv) HM.empty


    runPair :: (History, IntBindT m [RuleIB m ()]) -> IBRWST m [(TypedVar,RuleSetIB m)]
    runPair (History i t, m) =
      (\ (tv, m) -> (tv,HM.singleton (History i (tv:t)) m))
      <$> (getIBT m >>= (map mconcat . traverse runRule))

    runRule :: RuleIB m () -> IBRWST m [(TypedVar, IntBindT m [RuleIB m ()])]
    runRule (Act m) = getIBT m *> pure []
    runRule (Run m) = getIBT m >>= (map mconcat . traverse runRule)
    runRule (Watch v m) = pure [(v, m)]

-- | Set of rules that should be triggered when an action happens.
type RuleSet m = HashMap History (m [Rule m ()])
type RuleSetIB m = RuleSet (IntBindT m)
-}
