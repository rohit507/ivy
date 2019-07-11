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
import Ivy.GeneralError

import Ivy.Wrappers.IntMap (IntMap)
import qualified Ivy.Wrappers.IntMap as IM
import Ivy.Wrappers.IntSet (IntSet)
import qualified Ivy.Wrappers.IntSet as IS
import Ivy.Wrappers.IntGraph (IntGraph)
import qualified Ivy.Wrappers.IntGraph as IG
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.TypeMap.Dynamic.Alt (TypeMap, Item)
import qualified Data.TypeMap.Dynamic.Alt as TM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
-- import qualified Data.IntMap as M
-- import Data.TypeMap.Dynamic (TypeMap)
-- import qualified Data.TypeMap.Dynamic as TM

-- | Uninhabited type we use for our Item family.
data RelMap
type instance TM.Item RelMap t = HashMap t ETID

-- | Reader Monad Info
data Context where
  Context :: (Monad m, Typeable m) => {
    monadType :: TypeRep m
  , conf :: Config m
  , assumes :: Assumptions
  } -> Context


-- | General config info that only needs to be set once.
data Config m = Config {
    -- | How many times do we try to unify a single pair of elements before
    --   giving up hope that it will ever quiesce.
    maxCyclicUnifications :: Int
    -- | An action to generate a new unique ID. It's here because often we
    --   will want to generate UIDs in a context lower in the stack that isn't
    --   really aware of backtracking from using 'attempt'. That way we don't
    --   get ID collisions simply because a supply generated the same term.
    --
    --   We're not adding something to generate IDs to the monad stack
    --   because that seems like we're asking too much.
  , generateNewID :: m Int
  }


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
data Assumptions = Assumptions {
    -- | Assumption that a pair of terms are unified.
    unified :: HashSet (ETID,ETID)
    -- | Assumption that some pair of terms is structurally equal, without
    --   necessarily being unified.
  , equal :: HashSet (ETID,ETID)
    -- | Assumption that one term subsumes another.
  , subsumed :: HashSet (ETID,ETID)
  }

instance Semigroup Assumptions where
  (Assumptions a b c) <> (Assumptions a' b' c')
    = Assumptions (a <> a') (b <> b') (c <> c')

instance Monoid Assumptions where
  mempty = Assumptions mempty mempty mempty

-- | Runtime state of our term-graph thing.
data BindingState = BindingState {
     -- | Term Specific Information.
     termData :: IntMap ETermID TermState
   }

type BoundStateIB t m = BoundState t (IntBindT m)

-- | The state for a bound term, with type information.
data BoundState t m = BoundState {
       termValue :: Maybe (t (VarIB t m))
     -- | Relations from this term to other terms
     , relations :: TypeMap RelMap
     -- | Terms that ultimately point to this term
     , forwardedFrom :: IntSet (VarIB t m)
     -- | What terms does this one subsume?
     , subsumedTerms :: IntSet (VarIB t m)
     -- | Has this term been changed and not had any of its hooks run.
     , dirty :: !Bool
     }

-- | The unique state information we store for each term.
data TermState where
  Bound     :: (IBM e m, Term e t) => TypeRep t -> TypeRep m -> BoundState t m -> TermState
  Forwarded :: (IBM e m, Term e t) => TypeRep t -> TypeRep m -> TermID t -> TermState
  Errored   :: (IBM e m, Term e t) => TypeRep t -> TypeRep m -> e -> TermState

-- | The state of a newly inserted free term.
freeVarState :: proxy t -> BoundState t m
freeVarState _ = BoundState {
    termValue = Nothing
  , relations = TM.empty
  , forwardedFrom = IS.empty
  , subsumedTerms = IS.empty
  , dirty = True
  }

type IBRWST = RWST Context Assumptions BindingState

-- | Pure and Slow Transformer that allow for most of the neccesary binding
--   operations.
newtype IntBindT m a = IntBindT { getIBT :: IBRWST m a}

deriving newtype instance (Functor m) => Functor (IntBindT m)
deriving newtype instance (Monad m) => Applicative (IntBindT m)
deriving newtype instance (Monad m) => Monad (IntBindT m)
deriving newtype instance (MonadError e m) => MonadError e (IntBindT m)

instance (Monad m) => MonadState BindingState (IntBindT m)

instance (Monad m) => MonadReader Context (IntBindT m)

instance MonadTrans IntBindT where

  lift :: (Monad m) => m a -> IntBindT m a
  lift = IntBindT . lift

instance MonadTransControl IntBindT where

  type StT IntBindT a = (a, BindingState, Assumptions)
  liftWith f = IntBindT . rwsT $ \r s -> map (\x -> (x, s, mempty))
                                      (f $ \t -> runRWST (getIBT t) r s )
  restoreT mSt = IntBindT . rwsT $ \_ _ -> mSt
  {-# INLINABLE liftWith #-}
  {-# INLINABLE restoreT #-}

-- | Keep from having to repeatedly
type VarIB t m = Var t (IntBindT m)

instance ( Typeable t
         , Typeable m
         ) => MonadBind t (IntBindT m) where

  type Var t = VarID t

  freeVar :: forall t m e proxy.  (MonadError e (IntBindT m), Term e t)
    => proxy t -> IntBindT m (VarIB t m)
  freeVar _ = IntBindT $ do
    i <- newIdent
    setTermState i $ Bound (typeRep @t) (typeRep @m) $ freeVarState (typeRep @t)
    return i
    -- Generate a new identifier
    -- Add initial term-state to our state map

  lookupVar :: (MonadError e (IntBindT m), Term e t)
    => VarIB t m -> IntBindT m (Maybe (t (VarIB t m)))
  lookupVar = undefined
    -- get the correct termstate
    -- get the termvalue out of that termstate

  bindVar :: (MonadError e (IntBindT m), JoinSemiLattice1 e t)
    => VarIB t m -> t (VarIB t m) -> IntBindT m (VarIB t m)
  bindVar = undefined
    -- update the termState with the new varId
    -- Perform any neccesary bookkeeping
       -- move relation

-- | Generate a new internal identifier of some type.
--
--   First type parameter is the output ident type.
newIdent :: forall i m e m'. (IBM e m , Newtype i Int) => IBRWST m i
newIdent = ask >>= \ (Context trm config _) ->
  case eqTypeRep trm $ typeRep @(IntBindT m) of
    Nothing -> throwInvalidTypeFound trm (typeRep @m)
    Just HRefl -> map pack . getIBT $ generateNewID config

-- | Ensures that the type of the term state matches the type of the
--   input variable.
validateTermStateType :: forall t m e. (IBM e m, Term e t) => VarIB t m -> TermState -> IBRWST m ()
validateTermStateType _ st = case st of
  (Bound     trt trm _) -> validateTypes trt trm
  (Forwarded trt trm _) -> validateTypes trt trm
  (Errored   trt trm _) -> validateTypes trt trm

  where

    validateTypes :: (Typeable t', Typeable m') => TypeRep t' -> TypeRep m' -> IBRWST m ()
    validateTypes tt tm  = do
      case eqTypeRep tt $ typeRep @t of
        Nothing -> throwInvalidTypeFound tt (typeRep @t) :: IBRWST m ()
        Just HRefl -> pure ()
      case eqTypeRep tm $ typeRep @(IntBindT m) of
        Nothing -> throwInvalidTypeFound tm (typeRep @(IntBindT m))
        Just HRefl -> pure ()


-- | Gets the TermState for a variable, without further traversing
--   the network of connections to get to the final element.
getTermState :: (IBM e m, Term e t) => VarIB t m -> IBRWST m TermState
getTermState v = do
  td <- termData <$> get
  case IM.lookup (flattenVID v) td of
    Nothing -> throwNonexistentTerm v
    Just ts -> validateTermStateType v ts *> pure ts

-- | Sets the termState for a variable without additional bookkeeping.
setTermState :: (IBM e m, Term e t) => VarIB t m -> TermState -> IBRWST m ()
setTermState = undefined

-- | Potentially gets a termState for a variable throwing an error if the
--   type is incorrect. Does not traverse to find the final element.
getBoundState :: VarIB t m -> IBRWST m (Maybe (BoundStateIB t m))
getBoundState = undefined

-- | Updates the termState of a variable while performing other bookkeeping
--   tasks.
updateTermState :: VarIB t m -> TermState -> IBRWST m ()
updateTermState = undefined

-- | Finds the terminal element in a chain of forwarded terms. Performs
--   path compression during the lookup phase.
getBoundVar :: VarIB t m -> IBRWST m (VarIB t m)
getBoundVar = undefined

instance MonadUnify t (IntBindT m) where

  unify :: (JoinSemiLattice1 e t, MonadError e m)
    => VarIB t m -> VarIB t m -> IntBindT m (VarIB t m)
  unify = undefined
    -- check if the terms are structurally equal and return result
    -- check if the terms are unified wrt to assumptions and return result
    -- otherwise, start merging terms layer by layer.
       -- Bookkeeping for
           -- Properties
           -- forwardedSet

  equals :: (JoinSemiLattice1 e t, MonadError e m)
    => VarIB t m -> VarIB t m -> IntBindT m Bool
  equals = undefined
    -- check if terms are structurally equal
    -- check if terms are unified wrt to assumptions
    -- check if terms are equal wrt to assumptions.
    -- otherwise do layer by layer equality check

-- | Checks whether two terms are marked as having been unified in our
--   assumptions. If yes, then adds the corresponding unification term
--   to the read set and moves on.
assumeUnified :: VarIB t m -> VarIB t m -> IntBindT m (Maybe (VarIB t m))
assumeUnified = undefined

-- | Checks whether we have an assumption of equality, if yes then
--   writes out the equality to the read set.
assumeEquals :: VarIB t m -> VarIB t m -> IntBindT m Bool
assumeEquals = undefined

instance MonadSubsume t (IntBindT m) where

  -- TODO :: Okay so the question is how do we properly recurse? do we
  --        filter step by step, or what.
  subsume :: VarIB t m -> VarIB t m -> IntBindT m ()
  subsume = undefined
    -- check equality and assumptions
    -- add subsumption relationship to initial term
    -- mark as dirty

  subsumes :: VarIB t m -> VarIB t m -> IntBindT m Bool
  subsumes = undefined
    -- Check structuralEquality
    -- check equality and unity assumptions
    -- check subsume assumptions
    -- check layer by layer subsumption.


-- | Checks whether one term is subsumed by another in our assumptions.
assumeSubsumed :: VarIB t m -> VarIB t m -> IntBindT m Bool
assumeSubsumed = undefined

data TV t v = T (t (TV t v)) | V v

-- | Actually performs the subsumption operation while keeping track
--   of the set of currently assumed subsumptions that are required
--   for the operation to succeed
performSubsume :: VarIB t m -> VarIB t m -> IntBindT m ()
performSubsume = undefined
  -- Add assumption of these terms being subsumed.
  -- subsume single layer of terms by lifting subsume with the JoinSemiLattice

instance (Typeable p, Typeable m) => MonadProperty p (IntBindT m) where

  propertyOf :: (Property p t t', MonadBind t (IntBindT m), MonadBind t' (IntBindT m))
    => p -> VarIB t m -> IntBindT m (VarIB t' m)
  propertyOf = undefined
    -- Check if a property exists in the corresponding term
    -- If no, then create a freeVar and assign it to that property
    -- if yes, then get the term pointed to by the property in the map.


instance (MonadError e (IntBindT m), MonadAttempt m) => MonadAttempt (IntBindT m) where

  attempt :: IntBindT m (Either f b) -> (f -> IntBindT m b) -> IntBindT m b
  attempt = defaultLiftAttempt
              (\ (a,s,w) -> (((),s,w),a))
              (\ (((),s,w), a) -> (a,s,w))

-- TODO ::
--    - Property tests
--    - core implementation of unification
--

      -- Consider converting to a typed map, at least early on.
      -- TODO :: Should we keep a graph of term relationships or something?
      --         That would hopefully let us minimize the number of terms we
      --         update, and let us keep better track of subsumption, esp
      --         when a cycle occurs and a sequence of terms should be unified.
      --
      --   - Okay so we get three graphs
      --       - Basic dependency graph w/in a term type
      --       - subsumption graph where cycle detection can lead to the
      --         collapsing of term
      --       - edge-labeled relationship graph which we can use to
      --         project or inject rules when needed.
      --
      --   - What happens if we're strict w.r.t to hooks?
      --       - well, we open ourselves up to infinite cycles or indefinite
      --         expansion of the graph as rules trigger and re-trigger.
      --   - What happens if we're lazy?
      --       - we have to do more work to keep proper track of whether
      --         we have cycles in chains of actions, and them resolve them
      --         somehow.
      --         - So let's walk through that : We have a <- b <- c <- a
      --           we start when b changes and we run the relevant rules
      --           if c is also dirty, then we run through those terms.
      --           if a is dirty then we can run through its rules
      --           well, then we hit b again.
      --           - At which point we notice that b is practically dirty
      --             and move through the relevant steps again.
      --           - Of course, we could be co-inductive and assume that
      --             b is clean and just run one iteration of the cycle.
      --             - when we recurse back to that first call then we could
      --               notice that b was in the set of operations we actually
      --               leaned on our co-inductive assumption.
      --             - And then what? if we notice that we have changed b
      --               we rerun the process?
      --             - well, we could put a counter down and limit the
      --               number of cycles to some parameter?
      --   - Of course laziness needs an additional assumption for it to
      --     be correct which is that no rule will take a bottom and
      --     turn it into something higher than bottom on the lattice.
      -- Sigh :| i need to think about testing all this stuff, especially
      -- ensuring that the partial order / lattice properties are well met.
      -- Likewise, Testing the correctness of hooks would be super nice.
      --
      -- Hooks are going to be the hard part here, since we need to
      -- basically do some silly continuation based stuff that
      -- allows us to split and merge hooks.
      --
      -- So we need a bunch of specific properties for a hook:
      --   it has a nominal breadth and height, where breadth is the number of
      --   parallel actions composed into a single chain.
      --   The height is number of remaining steps in the longest of those
      --   actions.
      --
      -- We need to make sure that, unless an external bind is applied, then
      -- we always reduce the number of steps remaining.
      --
      -- Thankfully, the hook layer should be pretty independent of the
      -- attempt structure, especially when we can just keep an old state
      -- hiding somewhere and swap it in when we mess up. Having that model
      -- hopefully means we don't have to super picky (for now) about keeping
      -- hooks revertible.
      --
      -- So Okay, what can these hooks do?
      --    Unify / Subsume / Bind etc...
      --    Watch for changes in a term, filter on some upwards
      --       closed property
      --    Spawn multiple parallel hooks
      --    Ideally we would be able:
      --        detect that trees are identical and keep from duplicating them
      --        prune action trees that are unachiveable.
      --    hold until a term is subsumed by another, hold until terms are
      --    equal.
      --
      --    I guess there will also probably be some way to update a hook as
      --    bindings change.
      --
      -- Boy oh boy :V and then once that's done we can focus on wrapping things
      -- up neatly. And preventing a lot of single level decomp
