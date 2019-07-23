
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
import Ivy.Wrappers.IDs

import Ivy.Wrappers.IntMap (IntMap)
import qualified Ivy.Wrappers.IntMap as IM
import Ivy.Wrappers.IntSet (IntSet)
import qualified Ivy.Wrappers.IntSet as IS
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.TypeMap.Dynamic (TypeMap, Item)
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


-- | Uninhabited type we use for our Item family.
data RelMap
type instance TM.Item RelMap t = TypedVar

data RuleMap
type instance TM.Item RuleMap t = DefaultRule t

data DefaultRule t where
  DR :: TypeRep m -> [TermID t -> Rule (IntBindT m) ()] -> DefaultRule t

data Context where
  Context :: forall m. (Monad m, Typeable m) =>
    { _monadType  :: TypeRep m
    , _configData  :: Config m
    , _assumptions :: Assuming
    } -> Context


-- | General config info that only needs to be set once.

data Config m = Config {
    -- | How many times do we try to unify a single pair of elements before
    --   giving up hope that it will ever quiesce.
    _maxCyclicUnifications :: Int
    -- | An action to generate a new unique ID. It's here because often we
    --   will want to generate UIDs in a context lower in the stack that isn't
    --   really aware of backtracking from using 'attempt'. That way we don't
    --   get ID collisions simply because a supply generated the same term.
    --
    --   We're not adding something to generate IDs to the monad stack
    --   because that seems like we're asking too much.
  , _generateNewID :: m Int
  }

-- | Basic default configuration.
defaultConfig :: (MonadIO m) => m (Config m)
defaultConfig = do
  supply <- liftIO $ newIORef =<< newSupply
  let genID = liftIO $ atomicModifyIORef supply (flip2 . freshId)
  pure $ Config 200 genID
  where
    flip2 (a,b) = (b,a)

-- | A set of assumptions about the term-graph that were either made or
--   relied upon. We use this to properly handle cyclic terms and co-inductive
--   reasoning in general.
--
--   For instance, when trying to unify two terms, you don't want to get caught
--   in a cycle of repeatedly unifying elements. So you proceed unifying
--   subterms with an assumption that the parent terms are already unified.
--
--   In the writer slot, this allows for one to get those assumptions which
--   were hit when this process happened.

data Assuming = Assuming {
    -- | Assumption that a pair of terms are unified.
    _unified  :: HashSet (TypedVar, TypedVar)
    -- | Assumption that some pair of terms is structurally equal, without
    --   necessarily being unified.
  , _equal    :: HashSet (TypedVar, TypedVar)
    -- | Assumption that one term subsumes another.
  , _subsumed :: HashSet (TypedVar, TypedVar)
  , _clean :: HashSet TypedVar
  }

-- | Check if two sets of assumptions intersect
assumingIntersects :: Assuming -> Assuming -> Bool
assumingIntersects (Assuming a b c) (Assuming a' b' c')
  = not $  HS.null (HS.intersection a a')
        && HS.null (HS.intersection b b')
        && HS.null (HS.intersection c c')


-- | Get the intersection of two sets of assumptions
assumingIntersection :: Assuming -> Assuming -> Assuming
assumingIntersection (Assuming a b c) (Assuming a' b' c')
  = Assuming (HS.intersection a a')
             (HS.intersection b b')
             (HS.intersection c c')
data Assumption
  = TypedVar `IsUnifiedWith` TypedVar
  | TypedVar `IsEqualTo`     TypedVar
  | TypedVar `IsSubsumedBy`  TypedVar
  | IsClean TypedVar

-- | Convinient builder for an assumption that strips type information
isUnifiedWith :: forall t e. (Term e t) => TermID t -> TermID t -> Assumption
isUnifiedWith a b = (typedTID @t @e a) `IsUnifiedWith` (typedTID @t @e b)

-- | Convinient builder for an assumption that strips type information
isEqualTo :: forall t e. (Term e t) => TermID t -> TermID t -> Assumption
isEqualTo a b = (typedTID @t @e a) `IsEqualTo` (typedTID @t @e b)

-- | Convinient builder for an assumption that strips type information
isSubsumedBy :: forall t e. (Term e t) => TermID t -> TermID t -> Assumption
isSubsumedBy a b = (typedTID @t @e a) `IsSubsumedBy` (typedTID @t @e b)

assumeClean :: forall t e. (Term e t) => TermID t -> Assumption
assumeClean = IsClean . typedTID @t @e

buildAssuming :: Assumption -> Assuming
buildAssuming = undefined

instance Semigroup Assuming where
  (Assuming a b c) <> (Assuming a' b' c')
    = Assuming (a <> a') (b <> b') (c <> c')

instance Monoid Assuming where
  mempty = Assuming mempty mempty mempty

-- | Runtime state of our term-graph thing.
data BindingState = BindingState {
     _termData      :: HashMap ETID   TermState
   , _ruleData      :: HashMap RuleID RuleState
   , _dependencyMap :: AdjacencyMap InternalID
   -- | A lookup table we use to find the rule corresponding
   --   to some known history. This is generally kept fresh by
   --   traversal when a term is forwarded.
   , _ruleLookup    :: HashMap RuleHistory RuleID
   -- | set of dirty terms that require cleaning.
   , _dirtySet      :: HashSet ETID
   , _defaultRules  :: TypeMap RuleMap
   }


-- | A generic identifier that lets us differentiate between terms and rules.
data InternalID
  = TID TypedVar
  | RID RuleID
  deriving (Eq, Ord, Generic, Hashable)

-- | The unique state information we store for each term.
data TermState where
  Bound     :: (Term e t) => TypeRep t -> TypeRep e -> BoundState t -> TermState
  Forwarded :: (Term e t) => TypeRep t -> TypeRep e -> TermID     t -> TermState

-- | The state for a bound term, with type information
data BoundState t = BoundState {
       _termType :: TypeRep t
     , _termValue :: Maybe (t (TermID t))
     -- | Relations from this term to other terms
     , _relations :: TypeMap RelMap
     -- | What terms does this one subsume?
     , _subsumedTerms :: IntSet (TermID t)
     }

freeBoundState :: (Typeable t) => BoundState t
freeBoundState = BoundState typeRep Nothing TM.empty IS.empty

-- | The thunk for a rule itself and its metadata
data RuleState where
  RuleState ::
    { _monadType :: TypeRep m
    , _rule    :: IntBindT m [Rule (IntBindT m) ()]
    } -> RuleState

-- | The history of a rule which, when freshened, served as a unique identifier.
data RuleHistory = RuleHistory
  { _ident :: RuleID -- The identifier of the initial rule in the history
  , _terms :: [(RuleAction,TypedVar)] -- A list of variables that are touched
  } deriving (Eq, Ord, Generic, Hashable)

-- | The type of action this rule performed on a given variable.
data RuleAction = LookupTerm | WriteTerm
  deriving (Eq, Ord, Show, Generic, Hashable)

-- | This should probably be done with a free monad but this is a monad for
--   rules we can execute to edit or manipulate terms.
data Rule m a where
  Watch :: (Typeable t, IBTM' e t m) =>
    { watched    :: TermID t
    , steps    :: m [Rule m a]
    } -> Rule m a
  Update :: (Typeable t, IBTM' e t m) =>
    { updating :: TermID t
    , update :: m (t (TermID t))
    , steps :: m [Rule m a]
    } -> Rule m a
  Run :: m [Rule m a] -> Rule m a
  Act :: m a -> Rule m a

instance (Functor m) => GHC.Base.Functor (Rule m) where
  fmap f (Watch w s) = Watch w ((map . map $ map f) s)
  fmap f (Update t u s) = Update t u ((map . map $ map f) s)
  fmap f (Run m) = Run $ (map . map $ map f) m
  fmap f (Act m) = Act . map f $ m

instance (Monad m) => Applicative (Rule m) where
  pure = Act . pure
  (<*>) = ap

instance (Monad m) => Monad (Rule m) where
  (Act m) >>= k = Run . map (:[]) $ k <$> m
  (Run m) >>= k = Run $ (map $ map (>>= k)) m
  (Watch w s) >>= k = Watch w $ map (map (>>= k)) s
  (Update t u s) >>= k = Update t u $ map (map (>>= k)) s

instance (Monad m) => MonadFail (Rule m) where
  fail _ = Run $ pure []

-- | the full set of constraints we use here and there
type IBTM' e t m = (IBTM e t m, MonadBind t (IntBindT m))

-- | Newtype for the fully loaded monad transformer.
type IBRWST = RWST Context Assuming BindingState

-- | Pure and Slow Transformer that allow for most of the neccesary binding
--   operations.
newtype IntBindT m a = IntBindT { getIBT :: IBRWST m a}

deriving newtype instance (Functor m) => Functor (IntBindT m)
deriving newtype instance (Monad m) => Applicative (IntBindT m)
deriving newtype instance (Monad m) => Monad (IntBindT m)
deriving newtype instance (MonadError e m) => MonadError e (IntBindT m)
deriving newtype instance (Monad m) => MonadState BindingState (IntBindT m)
deriving newtype instance (Monad m) => MonadReader Context (IntBindT m)

-- $ Derived Field Lenses
{-
class HasMonadType s t a b | s b -> t, t a -> s where
  monadType :: Lens s t a b

class HasConfigData s t a b | s a -> t b, t b -> s a, s b -> t a where
  configData :: Lens s t a b

class HasAssumptions s t a b | s b -> t, t a -> s where
  assumptions :: Lens s t a b
instance forall m. (Typeable m) => HasMonadType Context Context (Maybe (TypeRep m)) (Maybe (TypeRep m)) where
  monadType = lens getter setter
    where
      getter (Context mt _ _) = do
        HRefl <- eqTypeRep mt (typeRep @m)
        pure mt

      setter :: Context -> Maybe (TypeRep m) -> Context
      setter c _ = fromMaybe c

instance forall m.(Typeable m) =>  HasConfigData Context (Maybe Context) (Maybe (Config m)) (Config m) where
  configData = lens getter setter
    where
      getter (Context mt c _) = do
        HRefl <- eqTypeRep mt (typeRep @m)
        pure c

      setter (Context mt _ a) c' = do
        HRefl <- eqTypeRep mt (typeRep @m)
        pure $ Context mt c' a

instance HasAssumptions Context Context Assuming Assuming where
  assumptions = lens _assumptions (\ c a -> c{_assumptions=a})
 -}

makeFieldsNoPrefix ''Context
makeFieldsNoPrefix ''Config
makeFieldsNoPrefix ''Assuming
makeFieldsNoPrefix ''BindingState
makePrisms ''InternalID
makePrisms ''TermState
makeFieldsNoPrefix ''BoundState
makeFieldsNoPrefix ''RuleHistory
makeFieldsNoPrefix ''RuleState
makePrisms ''RuleAction

-- | a getter for typed config data
toConfig :: forall m. (Typeable m) => Getting (Maybe (Config m)) Context (Maybe (Config m))
toConfig = to $ \ (Context tm c _) -> do
  HRefl <- eqTypeRep tm (typeRep @m)
  pure c



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
  pure v

-- | Looks up a variable after ensuring that it's been cleaned and updated.
lookupVarT :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m (Maybe (t (TermID t)))
lookupVarT t = do
  t' :: TermID t <- getRepresentative t
  cleanTerm t'
  let et' = crushTID t'
  (use $ termData . at @(HashMap ETID TermState) et') >>= \case
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
    when (not $ HS.null lostDeps) $ do
      traverse_ (removeDependency @t tv') $ HS.toList lostDeps
      markDirty v'
    when (not $ HS.null newDeps) $ do
      traverse_ (addDependency    @t tv') $ HS.toList newDeps
      markDirty v'
  setTermValue v' nt
  pure v'

-- | Just sets the term value, doesn't do any bookkeeping
setTermValue :: forall t m e. (IBTM' e t m)
             => TermID t -> t (TermID t) -> IBRWST m ()
setTermValue = undefined

-- | Runs through the entire
getTermDeps :: t (TermID t) -> HashSet InternalID
getTermDeps = undefined

-- | removes a dependency from the dependency graph
removeDependency :: forall t m e. (IBTM' e t m)
               => InternalID -> InternalID -> IBRWST m ()
removeDependency = undefined

addDependency :: forall t m e. (IBTM' e t m)
             => InternalID -> InternalID -> IBRWST m ()
addDependency = undefined

getBoundData :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m (BoundState t)
getBoundData = undefined

setTermData :: forall t m e. (IBTM' e t m)
            => TermID t -> TermState -> IBRWST m ()
setTermData i s = termData . at (crushTID i) .= Just s

applyDefaultRules :: forall t m e. (IBTM' e t m)
                  => TermID t -> IBRWST m ()
applyDefaultRules = undefined

addToDepGraph :: InternalID -> IBRWST m ()
addToDepGraph = undefined

-- | This will go on forever if your rules don rules don't settle down
cleanTerm :: forall t m e. (IBTM' e t m) => TermID t -> IBRWST m ()
cleanTerm t = (view $ toConfig @m) >>= \case
  Nothing -> panic "invalid config"
  Just c  -> go 0 t (c ^. maxCyclicUnifications)

  where

    go n t max = do
      when (n > max) $ panic "Cycle didn't quiesce in time"
      t' <- getRepresentative t
      whenM (isDirty t') $ do
        -- If we can clean up all our child terms
        markClean t
        markClean t'
        cleanDependencies t'
        applySubsumptions t'
        runRules t'
      go (n + 1) t' max

isDirty :: forall t m e. () => TermID t -> IBRWST m Bool
isDirty = undefined


withAssumption :: forall t m e. () => Assumption -> IBRWST m a -> IBRWST m (a, Bool)
withAssumption = undefined

getDependencies :: forall t m e. () => TermID t -> IBRWST m (HashSet InternalID)
getDependencies = undefined

-- | Flags all child terms as dirty as well, stepping through what rules
--   can modify this term.
markDirty :: forall t m e. () => TermID t -> IBRWST m ()
markDirty = undefined

markClean :: forall t m e. () => TermID t -> IBRWST m ()
markClean = undefined

getRepresentative :: forall t m e. () => TermID t -> IBRWST m (TermID t)
getRepresentative = undefined

-- | Returns nothing if the terms aren't equal, otherwise it returns a list
--   of terms that should be unified to unify the input terms.
--   the returned list is as topologically sorted as possible given the
--   existence of cycles.
equalsT :: forall t m e. ()
   => TermID t -> TermID t -> IBRWST m (Maybe [(TypedVar, TypedVar)])
equalsT = undefined

-- | unifies all the various terms as needed.
unifyT :: forall t m e. () => TermID t -> TermID t -> IBRWST m (TermID t)
unifyT = undefined

-- | Like equalsT but returns the set of subsumptions that need to occour.
subsumesT :: forall t m e. ()
  => TermID t -> TermID t -> IBRWST m (Maybe [(TypedVar, TypedVar)])
subsumesT = undefined

-- | ensures the first term subsumes the second, returns the ident for
--   the second term .
subsumeT :: forall t m e. ()
  => TermID t -> TermID t -> IBRWST m (TermID t)
subsumeT = undefined

propertyOfT :: forall p t t' m e. ()
  => p -> TermID t -> IBRWST m (TermID t')
propertyOfT = undefined

addGeneralRuleT :: forall t m e. ()
  => (TermID t -> Rule (IntBindT m) ()) -> IBRWST m ()
addGeneralRuleT = undefined

addSpecializedRuleT :: forall t m e. ()
  => Rule (IntBindT m) () -> IBRWST m ()
addSpecializedRuleT = undefined

type VarIB t m = Var t (IntBindT m)

{-
instance (IBTM e t m) => MonadBind t (IntBindT m) where

  type Var t = VarID t

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
