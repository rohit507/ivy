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

import Ivy.Wrappers.IntMap (IntMap)
import qualified Ivy.Wrappers.IntMap as IM
import Ivy.Wrappers.IntSet (IntSet)
import qualified Ivy.Wrappers.IntSet as IS
import Ivy.Wrappers.IntGraph (IntGraph)
import qualified Ivy.Wrappers.IntGraph as IG
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import Data.TypeMap.Dynamic.Alt (TypeMap, Item)
import qualified Data.TypeMap.Dynamic as TM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
-- import qualified Data.IntMap as M
-- import Data.TypeMap.Dynamic (TypeMap)
-- import qualified Data.TypeMap.Dynamic as TM

-- | Uninhabited type we use for our Item family.
--
--   TODO :: Modify this so that we can support non-singlton relationmaps.
data RelMap

data TypedVar where
  TVar :: (IBTM' e t m) => TypeRep t -> TypeRep m -> VarIB t m -> TypedVar
type instance TM.Item RelMap t = TypedVar

-- | Reader Monad Info
data Context where
  Context :: (Monad m, Typeable m) => {
    monadType :: TypeRep m
  , conf :: Config m
  , assumes :: Assuming
  } -> Context


type IBTM' e t m = (IBTM e t m, Show (t (VarIB t m)))

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
data Assuming = Assuming {
    -- | Assumption that a pair of terms are unified.
    unified :: HashSet (ETID,ETID)
    -- | Assumption that some pair of terms is structurally equal, without
    --   necessarily being unified.
  , equal :: HashSet (ETID,ETID)
    -- | Assumption that one term subsumes another.
  , subsumed :: HashSet (ETID,ETID)
  }

data Assumption
  = ETID `IsUnifiedWith` ETID
  | ETID `IsEqualTo`     ETID
  | ETID `IsSubSumedBy`  ETID

instance Semigroup Assuming where
  (Assuming a b c) <> (Assuming a' b' c')
    = Assuming (a <> a') (b <> b') (c <> c')

instance Monoid Assuming where
  mempty = Assuming mempty mempty mempty

-- | Runtime state of our term-graph thing.
data BindingState = BindingState {
     -- | Term Specific Information.
     termData :: IntMap ETermID TermState
   }

type BoundStateIB t m = BoundState t (IntBindT m)

-- | The state for a bound term, with type information
data BoundState t m = BoundState {
       termValue :: Maybe (t (VarID t m))
     -- | Relations from this term to other terms
     , relations :: TypeMap RelMap
     -- | Terms that ultimately point to this term
     , forwardedFrom :: IntSet (VarID t m)
     -- | What terms does this one subsume?
     , subsumedTerms :: IntSet (VarID t m)
     -- | Has this term been changed and not had any of its hooks run.
     , dirty :: !Bool
     }

-- | The unique state information we store for each term.
data TermState where
  Bound     :: (IBM e m, Term e t) => TypeRep t -> TypeRep m -> BoundState t m -> TermState
  Forwarded :: (IBM e m, Term e t) => TypeRep t -> TypeRep m -> VarIB t m -> TermState
  -- Errored   :: (IBTM' e t m, Typeable e)
    => TypeRep t -> TypeRep m -> TypeRep e -> e  -> TermState

-- | The state of a newly inserted free term.
freeVarState :: forall t m. BoundState t m
freeVarState = BoundState {
    termValue = Nothing
  , relations = TM.empty
  , forwardedFrom = IS.empty
  , subsumedTerms = IS.empty
  , dirty = True
  }

-- | The term state of a newly inserted term
freeTermState :: forall t m e. (IBTM' e t m) => VarIB t m -> TermState
freeTermState _ = Bound (typeRep @t) (typeRep @m) freeVarState

type IBRWST = RWST Context Assuming BindingState

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

  type StT IntBindT a = (a, BindingState, Assuming)
  liftWith f = IntBindT . rwsT $ \r s -> map (\x -> (x, s, mempty))
                                      (f $ \t -> runRWST (getIBT t) r s )
  restoreT mSt = IntBindT . rwsT $ \_ _ -> mSt
  {-# INLINABLE liftWith #-}
  {-# INLINABLE restoreT #-}

-- | Keep from having to repeatedly
type VarIB t m = Var t (IntBindT m)

instance (forall e.
           MonadError e (IntBindT m)
         , MonadError e m
         , IBTM' e t m) => MonadBind t (IntBindT m) where

  type Var t = VarID t

  freeVar :: IntBindT m (VarIB t m)
  freeVar = IntBindT $ freeVarT

  lookupVar :: VarIB t m -> IntBindT m (Maybe (t (VarIB t m)))
  lookupVar = IntBindT . lookupVarT

  bindVar :: VarIB t m -> t (VarIB t m) -> IntBindT m (VarIB t m)
  bindVar v t = IntBindT $ bindVarT v t

-- | Generate a new internal identifier of some type.
--
--   First type parameter is the output ident type.
newIdent :: forall i m e. (IBM e m , Newtype i Int) => IBRWST m i
newIdent = ask >>= \ (Context trm config _) -> matchType @m trm
    (throwInvalidTypeFound trm (typeRep @m))
    (\ HRefl -> lift . map pack $ generateNewID config)

-- | Create a free var in IBRWST
freeVarT ::forall t m e. (IBTM' e t m) => IBRWST m (VarIB t m)
freeVarT = do
  i <- newIdent @(VarIB t m)
  setTermState i $ freeTermState i
  pure i

-- | When looking up a variable we need to find its representative
--
--   Performs additional bookkeeping.
lookupVarT :: forall t m e. (IBTM' e t m)
           => VarIB t m -> IBRWST m (Maybe (t (VarIB t m)))
lookupVarT v = do
  v' <- getRepresentative v
  termValue <$> getBoundState v'

-- | Binds a variable to a term, performs additional bookkeeping
bindVarT :: forall t m e. (IBTM' e t m)
         => VarIB t m -> t (VarIB t m) -> IBRWST m (VarIB t m)
bindVarT v t = do
    v' <- getRepresentative v
    modifyBoundState v' (pure . modif)
    pure v'
  where
    modif s@BoundState{..} = s{termValue = Just t}

-- | perform some action if types don't match
matchType :: forall t t' a. (Typeable t)
           => TypeRep t' -> a -> (t :~~: t' -> a) -> a
matchType tr err succ = case eqTypeRep tr (typeRep @t) of
  Nothing -> err
  Just HRefl -> succ HRefl

-- | Matches a pair of types instead of just one.
matchType2 :: forall t m t' m' a. (Typeable t, Typeable m)
           => TypeRep t' -> a
           -> TypeRep m' -> a
           -> (t :~~: t' -> m :~~: m' -> a)
           -> a
matchType2 tt errt tm errm succ =
  matchType @t tt errt
    (\ rt -> matchType @m tm errm (\ rm -> succ rt rm))



-- | Ensures that the type of the term state matches the type of the
--   input variable.
validateTermStateType :: forall t m e. (IBTM' e t m)
                      => VarIB t m -> TermState -> IBRWST m ()
validateTermStateType _ st = case st of
  (Bound     trt trm _  ) -> validateTypes trt trm
  (Forwarded trt trm _  ) -> validateTypes trt trm
  --(Errored   trt trm _ _) -> validateTypes trt trm

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
getTermState :: (IBTM' e t m) => VarIB t m -> IBRWST m TermState
getTermState v = do
  td <- termData <$> get
  case IM.lookup (flattenVID v) td of
    Nothing -> throwNonexistentTerm v
    Just ts -> validateTermStateType v ts *> pure ts

-- | Sets the termState for a variable without additional bookkeeping.
--
--   FIXME :: If termState is an error, and the thing to be inserted is an error
--      merge the errors, otherwise trying to set an errored term should be
--      a nop
setTermState :: (IBTM' e t m) => VarIB t m -> TermState -> IBRWST m ()
setTermState var term = do
  validateTermStateType var term
  modify (\ b -> b{termData = IM.insert (flattenVID var) term $ termData b})

-- | Modifies the term state of something with a function, does not
--   do additional bookkeeping.
modifyTermState :: (IBTM' e t m)
                => VarIB t m
                -> (TermState -> IBRWST m TermState)
                -> IBRWST m ()
modifyTermState v f = getTermState v >>= f >>= setTermState v


-- | Potentially gets a BoundState for a variable throwing an error if the
--   type is incorrect. Does not traverse to find the final element.
getBoundState :: forall t m e. (IBTM' e t m) => VarIB t m -> IBRWST m (BoundStateIB t m)
getBoundState v = getTermState v >>= \case
  (Bound tt tm bs) -> matchType2 @t @(IntBindT m)
     tt (throwInvalidTypeFound tt (typeRep @t))
     tm (throwInvalidTypeFound tm (typeRep @(IntBindT m)))
     (\ HRefl HRefl -> pure bs)
  _ -> throwExpectedBoundState v

-- | Sets the boundState of a trm
setBoundState :: forall t m e. (IBTM' e t m) => VarIB t m -> BoundStateIB t m -> IBRWST m ()
setBoundState v = modifyTermState v . const . pure . Bound typeRep typeRep

-- | Modifies the bound state of a term
modifyBoundState :: forall t m e. (IBTM' e t m)
                 => VarIB t m
                 -> (BoundStateIB t m -> IBRWST m (BoundStateIB t m))
                 -> IBRWST m ()
modifyBoundState v f =
  getBoundState v >>= map (Bound typeRep typeRep) . f >>= setTermState v

-- | Potentially gets a forwarded var for a variable throwing an error if the
--   type is incorrect. Does not traverse to find the final element.
getForwardingVar :: forall t m e. (IBTM' e t m) => VarIB t m -> IBRWST m (Maybe (VarIB t m))
getForwardingVar v = getTermState v >>= \case
  (Forwarded tt tm i) -> matchType2 @t @m
     tt (throwInvalidTypeFound tt (typeRep @t))
     tm (throwInvalidTypeFound tm (typeRep @m))
     (\ HRefl HRefl -> pure $ Just i)
  _ -> pure Nothing


-- | Tries to get the error corresponding to a particular term.
--   Does not try to traverse the forwarding chain.
getTermError :: forall t m e. (IBTM' e t m) => VarIB t m -> IBRWST m (Maybe e)
getTermError v = getTermState v >>= \case
  (Errored _ _ te i) -> matchType @e
     te (throwInvalidTypeFound te (typeRep @e))
     (\ HRefl -> pure $ Just i)
  _ -> pure Nothing

-- | Finds the Representative element for a Var in our disjoint set structure.
--
--   Element returned should always be an Error or a Bound Term.
--   Forwards paths as needed.
getRepresentative :: forall t m e. (IBTM' e t m) => VarIB t m -> IBRWST m (VarIB t m)
getRepresentative v = getForwardingVar v >>= \case
  Nothing -> pure v
  Just v' -> do
    v'' <- getRepresentative v'
    when (v' /= v'') $ setTermState v (Forwarded typeRep typeRep v'')
    pure v''

instance (forall e. IBTM' e t m, Show (t (VarIB t m))) => MonadUnify t (IntBindT m) where

  unify :: VarIB t m -> VarIB t m -> IntBindT m (VarIB t m)
  unify a b = IntBindT $ unifyT a b

  equals :: VarIB t m -> VarIB t m -> IntBindT m Bool
  equals a b = IntBindT $ equalsT a b

-- | Unify two terms in IBRWST and return the resulting outcome.
unifyT :: Monad m => VarIB t m -> VarIB t m -> IBRWST m (VarIB t m)
unifyT a b
  | a == b = pure a
  | otherwise = undefined
     -- check if unification assumed
     -- check that terms are related
     -- check that
     -- while assuming unification
        -- unify all subterms if possible
     -- unify the last level of the r term


-- | Check whether two terms are equivalent up to unification of various terms
equalsT :: Monad m => VarIB t m -> VarIB t m -> IBRWST m Bool
equalsT a b
  | a == b = pure True
  | otherwise = undefined
    -- Check if unification or requality assumed
    --

-- | Unifies a single level of terms, with the assumption that they are both
--   representatives of their category, and that all their subterms are properly
--   unified.
unifyLevel :: (IBTM' e t m) => VarIB t m -> VarIB t m -> IBRWST m (VarIB t m)
unifyLevel a b = do
  bsa <- getBoundState a
  modifyBoundState b (mergeBoundState a bsa)
  forwardTo a b

-- | Forwards the first var to the second, returns the second var.
forwardTo :: (IBTM' e t m) => VarIB t m -> VarIB t m -> IBRWST m (VarIB t m)
forwardTo from to = do
  modifyTermState from (const . pure $ Forwarded typeRep typeRep to)
  pure to

-- | Merge two bound states if possible. Can trigger unification of relations.
--   will verify that subterms are properly unified.
mergeBoundState :: forall e t m. (IBTM' e t m)
                => VarIB t m -- ^ from
                -> BoundStateIB t m -- ^ from
                -> BoundStateIB t m -- ^ to
                -> IBRWST m (BoundStateIB t m)
mergeBoundState fromVar BoundState{termValue=ftv
                               , relations=fr
                               , forwardedFrom=ff
                               , subsumedTerms=fs
                               }
                BoundState{termValue=ttv
                             ,relations=tr
                             ,forwardedFrom=tf
                             ,subsumedTerms=ts
                             }
  = BoundState <$> matchTerms ftv ttv
               <*> mergeRels tr
               <*> mergeForwarded ff tf
               <*> mergeSubsumed  fs ts
               <*> pure True

  where

    matchTerms Nothing a = pure a
    matchTerms a Nothing = pure a
    matchTerms (Just ftv) (Just ttv) = do
      canonFTV <- traverse getRepresentative ftv
      canonTTV <- traverse getRepresentative ttv
      when (not $ liftEq (==) canonFTV  canonTTV)
        $ throwTermsNotUnified canonFTV canonTTV
      pure $ Just canonTTV

    mergeRels :: TypeMap RelMap -> IBRWST m (TypeMap RelMap)
    mergeRels tr = TM.traverse mergeRelMap tr

    mergeRelMap :: forall p. (Typeable p) => Proxy p -> TypedVar -> IBRWST m TypedVar
    mergeRelMap proxy t@(TVar tt tm tv) = case TM.lookup proxy fr of
      Nothing -> pure t
      Just (TVar ft fm fv) -> mergeTypedVars tt tm ft fm tv fv

    mergeTypedVars ::forall ta ma tb mb e' e''.
                   (Typeable ta, Typeable ma, Typeable tb
                   ,Typeable mb, IBTM' e' ta ma, IBTM' e'' tb mb)
                   => TypeRep ta -> TypeRep ma
                   -> TypeRep tb -> TypeRep mb
                   -> VarIB ta ma -> VarIB tb mb -> IBRWST m TypedVar
    mergeTypedVars _ tma ttb tmb va vb = matchType2 @ta @ma
      ttb (throwInvalidTypeFound ttb (typeRep @ta))
      tmb (throwInvalidTypeFound tmb (typeRep @ma))
      (\ HRefl HRefl -> matchType2 @m @m
        tma (throwInvalidTypeFound tma (typeRep @m))
        tmb (throwInvalidTypeFound tma (typeRep @m))
        (\ HRefl HRefl -> matchType2 @e @e
          (typeRep @e') (throwInvalidTypeFound (typeRep @e') (typeRep @e))
          (typeRep @e'') (throwInvalidTypeFound (typeRep @e'') (typeRep @e))
          (\ HRefl HRefl -> TVar ttb (typeRep @m) <$> unifyT va vb )))


    mergeForwarded f t = pure $ f <> t <> IS.singleton fromVar

    mergeSubsumed f t = pure $ f <> t


  -- Ensure that a and b are both bound states / representatives
  -- if they are

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
    convert (IsSubSumedBy  a b) = mempty{subsumed=HS.singleton (a,b)}
    convert (IsUnifiedWith a b) = mempty{unified=HS.fromList [(a,b),(b,a)]}

    addedAssumptions = convert as

    modifyAssumptions b@Context{..} = b{assumes=assumes <> addedAssumptions}

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


-- | Checks whether two terms are marked as having been unified in our
--   assumptions. If yes, then adds the corresponding unification term
--   to the read set and moves on.
assumeUnified :: Monad m => VarIB t m -> VarIB t m -> IBRWST m Bool
assumeUnified v v' = (||) <$> check v v' <*> check v' v

  where

    check i i' = do
      let pair = (flattenVID i, flattenVID i')
      res <- HS.member pair . unified . assumes <$> ask
      when res . tell $ mempty{unified=HS.singleton pair}
      pure res

-- | Checks whether we have an assumption of equality, if yes then
--   writes out the equality to the read set.
assumeEquals :: Monad m => VarIB t m -> VarIB t m -> IBRWST m Bool
assumeEquals v v' = (||) <$> check v v' <*> check v' v

  where

    check i i' = do
      let pair = (flattenVID i, flattenVID i')
      res <- HS.member pair . equal . assumes <$> ask
      when res . tell $ mempty{equal=HS.singleton pair}
      pure res

instance (forall e. IBTM' e t m, Show (t (VarIB t m))) => MonadSubsume t (IntBindT m) where

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
assumeSubsumed :: Monad m => VarIB t m -> VarIB t m -> IBRWST m Bool
assumeSubsumed v v' = do
  let pair = (flattenVID v, flattenVID v')
  res <- HS.member pair . subsumed . assumes <$> ask
  when res . tell $ mempty{subsumed=HS.singleton pair}
  pure res

data TV t v = T (t (TV t v)) | V v

-- | Actually performs the subsumption operation while keeping track
--   of the set of currently assumed subsumptions that are required
--   for the operation to succeed
performSubsume :: VarIB t m -> VarIB t m -> IntBindT m ()
performSubsume = undefined
  -- Add assumption of these terms being subsumed.
  -- subsume single layer of terms by lifting subsume with the JoinSemiLattice

instance (Typeable p, Typeable m) => MonadProperty p (IntBindT m) where

  -- propertyOf :: p -> VarIB t m -> IntBindT m (VarIB t' m)
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
