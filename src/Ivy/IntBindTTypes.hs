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
import Ivy.Wrappers.IDs

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
    -- | Assumption that some term has been cleaned.
  , _clean :: HashSet TypedVar
  }

-- | Check if two sets of assumptions intersect
assumingIntersects :: Assuming -> Assuming -> Bool
assumingIntersects (Assuming a b c d) (Assuming a' b' c' d')
  = not $  HS.null (HS.intersection a a')
        && HS.null (HS.intersection b b')
        && HS.null (HS.intersection c c')
        && HS.null (HS.intersection d d')


-- | Get the intersection of two sets of assumptions
assumingIntersection :: Assuming -> Assuming -> Assuming
assumingIntersection (Assuming a b c d) (Assuming a' b' c' d')
  = Assuming (HS.intersection a a')
             (HS.intersection b b')
             (HS.intersection c c')
             (HS.intersection d d')

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
buildAssuming (a `IsUnifiedWith` b) = mempty{_unified=HS.fromList [(a,b),(b,a)]}
buildAssuming (a `IsEqualTo` b) = mempty{_equal=HS.fromList [(a,b),(b,a)]}
buildAssuming (a `IsSubsumedBy` b) = mempty{_subsumed=HS.singleton (a,b)}
buildAssuming (IsClean  a) = mempty{_clean=HS.singleton a}

instance Semigroup Assuming where
  (Assuming a b c d) <> (Assuming a' b' c' d')
    = Assuming (a <> a') (b <> b') (c <> c') (d <> d')

instance Monoid Assuming where
  mempty = Assuming mempty mempty mempty mempty

-- | Runtime state of our term-graph thing.
data BindingState = BindingState {
     _termData      :: HashMap TypedVar TermState
   , _ruleData      :: HashMap RuleID RuleState
   , _dependencyMap :: AdjacencyMap InternalID
   -- | A lookup table we use to find the rule corresponding
   --   to some known history. This is generally kept fresh by
   --   traversal when a term is forwarded.
   , _ruleLookup    :: RuleHistoryMap
   -- | set of dirty terms that require cleaning.
   , _dirtySet      :: HashSet TypedVar
   , _defaultRules  :: TypeMap RuleMap
   }

-- | This lets us (semi efficiently) look up the latest in carnation of a
--   given its history.
type RuleHistoryMap = HashMap RuleID (HashMap [(RuleAction,TypedVar)] RuleID)

-- | A generic identifier that lets us differentiate between terms and rules.
type InternalID = Either TypedVar RuleID

pattern TID :: TypedVar -> Either TypedVar RuleID
pattern TID a = Left a

pattern RID :: RuleID -> Either TypedVar RuleID
pattern RID a = Right a


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
     , _subsumedTerms :: HashSet (TermID t)
     }

freeBoundState :: (Typeable t) => BoundState t
freeBoundState = BoundState typeRep Nothing TM.empty HS.empty

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
type IBM' e m = (IBM e m)

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
makePrisms ''TermState
makeFieldsNoPrefix ''BoundState
makeFieldsNoPrefix ''RuleHistory
makeFieldsNoPrefix ''RuleState
makePrisms ''RuleAction
