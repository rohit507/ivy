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

import Ivy.MonadClasses
import Ivy.Prelude hiding (IntSet, IntMap)
import Control.Lens hiding (Context)
import Control.Lens.TH

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
import qualified Data.TypeMap.Dynamic.Alt as TM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
-- import qualified Data.IntMap as M
-- import Data.TypeMap.Dynamic (TypeMap)
-- import qualified Data.TypeMap.Dynamic as TM

-- | Uninhabited type we use for our Item family.
data RelMap m
type instance TM.Item (RelMap m) t = HashMap t ETID

-- | Reader Monad Info
data Context m = Context {
    _conf :: Config m
  , _assumes :: Assumptions m
  }


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
data Assumptions m = Assumptions {
    -- | Assumption that a pair of terms are unified.
    _unified :: HashSet (ETID,ETID)
    -- | Assumption that some pair of terms is structurally equal, without
    --   necessarily being unified.
  , _equal :: HashSet (ETID,ETID)
    -- | Assumption that one term subsumes another.
  , _subsumed :: HashSet (ETID,ETID)
  }

-- | Runtime state of our term-graph thing.
data BindingState m = BindingState {
     -- | Term Specific Information.
     _termData :: IntMap ETermID (TermState m)
   }


type BoundStateIB t m = BoundState t (IntBindT m)

-- | The state for a bound term, with type information.
data BoundState t m = BTS {
       _termValue :: Maybe (t (Var t m))
     -- | Relations from this term to other terms
     , _relations :: TypeMap (RelMap m)
     -- | Terms that ultimately point to this term
     , _forwardedFrom :: IntSet (Var t m)
     -- | What terms does this one subsume?
     , _subsumedTerms :: IntSet (Var t m)
     -- | Has this term been changed and not had any of its hooks run.
     , _dirty :: !Bool
     }

type TermStateIB m = TermState (IntBindT m)

-- | The unique state information we store for each term.
data TermState m where
  Bound     :: TypeRep t -> BoundState t m -> TermState m
  Forwarded :: TypeRep t -> TermID t -> TermState m
  Errored   :: (MonadError e m) => TypeRep t -> e -> TermState m

-- | The state of a newly inserted free term.
freeVarState :: proxy t -> BoundState t m
freeVarState = BTS {
    _termValue = Nothing
  , _relations = TM.empty
  , _forwardedFrom = IS.empty
  , _subsumedTerms = IS.empty
  , _dirty = True
  }

-- | Strip type information from a TermID
crushTID :: TermID t -> ETermID
crushTID = pack . unpack

-- | Add (potentially incorrect) type information to am ETID
unsafeExpandTID :: ETermID -> TermID t
unsafeExpandTID = pack . unpack

-- | Strip Monad information from a VerID
crushVID :: VarID t m -> TermID t
crushVID = pack . unpack

-- | Add (potentially incorrect) monad information to a VID
unsafeExpandVID :: TermID t -> VarID t m
unsafeExpandVID = pack . unpack

-- | Pure and Slow Transformer that allow for most of the neccesary binding
--   operations.
newtype IntBindT m a = IntBindT {
  getIBT :: RWST (Context       (IntBindT m))
                 (Assumptions  (IntBindT m))
                 (BindingState (IntBindT m)) m a
  }

deriving newtype instance (Functor m) => Functor (IntBindT m)
deriving newtype instance (Monad m) => Applicative (IntBindT m)
deriving newtype instance (Monad m) => Monad (IntBindT m)
deriving newtype instance (MonadError e m) => MonadError e (IntBindT m)

instance MonadTrans IntBindT where

  lift :: (Monad m) => m a -> IntBindT m a
  lift = IntBindT . lift

instance MonadTransControl IntBindT where

  type StT IntBindT a

-- | Keep from having to repeatedly
type VarIB t m = Var t (IntBindT m)

instance ( Typeable t
         , Typeable m
         , InternalError e m
         , MonadError e m
         ) => MonadBind t (IntBindT m) where

  type Var t (IntBindT m) = VarID t (IntBindT m)

  freeVar :: (MonadError e (IntBindT m), Unifiable e t)
    => proxy t -> IntBindT m (VarIB t m)
  freeVar = undefined
    -- Generate a new identifier
    -- Add initial term-state to our state map
    -- add variable to our intgraph.

  lookupVar :: (MonadError e (IntBindT m), Unifiable e t)
    => VarIB t m -> IntBindT m (Maybe (t (VarIB t m)))
  lookupVar = undefined
    -- get the correct termstate
    -- get the termvalue out of that termstate

  bindVar :: (MonadError e (IntBindT m), Unifiable e t)
    => VarIB t m -> t (VarIB t m) -> IntBindT m (VarIB t m)
  bindVar = undefined
    -- update the termState with the new varId
    -- Perform any neccesary bookkeeping
       -- move relation

-- | Generate a new internal identifier of some type.
--
--   First type parameter is the output ident type.
newIdent :: forall i m. (Newtype i Int) => IntBindT m i
newIdent = IBT $ undefined

-- | Gets the TermState for a variable, without further traversing
--   the network of connections to get to the final element.
getTermState :: VarIB t m -> IntBindT m (TermStateIB m)
getTermState = undefined

-- | A context for an error modifies an error to add additional metadata.
type ErrorContext e = e -> e

-- | Errors that are internal to our current library and are not due to
--   user error.
class InternalError e m where
  invalidTypeFound :: (Typeable a, Typeable b) => TypeRep a -> TypeRep b -> e
  gettingTermStateFor :: (Typeable t) => Var t m -> ErrorContext e
  gettingTerminalVarVor :: (Typeable t) => Var t m -> ErrorContext e

type InternalErr = InternalError

-- | Potentially gets a termState for a variable throwing an error if the
--   type is incorrect. Does not traverse to find the final element.
getBoundState :: VarIB t m -> IntBindT m (Maybe (BoundStateIB t m))
getBoundState = undefined

-- | Wholesale replacement of a termstate without any other bookkeeping
--   or the like.
setTermState :: VarIB t m -> TermStateIB m -> IntBindT m ()
setTermState = undefined

-- | Updates the termState of a variable while performing other bookkeeping
--   tasks.
updateTermState :: VarIB t m -> TermStateIB m -> IntBindT m ()
updateTermState = undefined

-- | Finds the terminal element in a chain of forwarded terms. Performs
--   path compression during the lookup phase.
getBoundVar :: VarIB t m -> IntBindT m (VarIB t m)
getBoundVar = undefined

instance MonadUnify t (IntBindT m) where

  unify :: (Unifiable e t, MonadError e m)
    => VarIB t m -> VarIB t m -> IntBindT m (VarIB t m)
  unify = undefined
    -- check if the terms are structurally equal and return result
    -- check if the terms are unified wrt to assumptions and return result
    -- otherwise, start merging terms layer by layer.
       -- Bookkeeping for
           -- Properties
           -- forwardedSet

  equals :: (Unifiable e t, MonadError e m)
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

instance MonadSubsume t m where

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


instance MonadAttempt (IntBindT m) where

  attempt :: IntBindT m (Either f b) -> (f -> IntBindT m b) -> IntBindT m b
  attempt = defaultLiftAttempt
              (\ (s,a) -> ((s, ()), a))
              (\ ((s, ()), a) -> (s, a))


makeClassy ''Context
makeClassy ''Config
makeClassy ''Assumptions
makeClassy ''BindingState
makeClassy ''BoundState
makeClassy ''TermState
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
