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

tVar :: forall t m e. (IBTM' e t m) => VarIB t m -> TypedVar
tVar = TVar (typeRep @t) (typeRep @m)

-- | Reader Monad Info

data Context where
  Context :: (Monad m, Typeable m) => {
    monadType :: TypeRep m
  , conf :: Config m
  , assumes :: Assuming
  } -> Context


type IBTM' e t m = (IBTM e t m, MonadBind t (IntBindT m))

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
  | ETID `IsSubsumedBy`  ETID

-- | Convinient builder for an assumption that strips type information
isUnifiedWith :: VarIB t m -> VarIB t m -> Assumption
isUnifiedWith a b = (flattenVID a) `IsUnifiedWith` (flattenVID b)

-- | Convinient builder for an assumption that strips type information
isEqualTo :: VarIB t m -> VarIB t m -> Assumption
isEqualTo a b = (flattenVID a) `IsEqualTo` (flattenVID b)

-- | Convinient builder for an assumption that strips type information
isSubsumedBy :: VarIB t m -> VarIB t m -> Assumption
isSubsumedBy a b = (flattenVID a) `IsSubsumedBy` (flattenVID b)

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
  --  => TypeRep t -> TypeRep m -> TypeRep e -> e  -> TermState

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
deriving newtype instance (Monad m) => MonadState BindingState (IntBindT m)
deriving newtype instance (Monad m) => MonadReader Context (IntBindT m)

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

-- | Performs updates to the term that can get rid of dirty flags if needed

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
setTermState :: (IBTM' e t m) => VarIB t m -> TermState -> IBRWST m ()
setTermState var term = whileSettingTermStateOf var $ do
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
setBoundState v n = modifyBoundState v (\ _ -> pure n)

-- | Modifies the bound state of a term, automatically dirties term if
--   there's a change.
modifyBoundState :: forall t m e. (IBTM' e t m)
                 => VarIB t m
                 -> (BoundStateIB t m -> IBRWST m (BoundStateIB t m))
                 -> IBRWST m ()
modifyBoundState v f = do
  bs <- getBoundState v
  bs' <- f bs
  when (bs /= bs') $ setTermState v (Bound typeRep typeRep bs'{dirty=True})

-- | Checks whether two bound states are semantically different
isBoundStateUpdated :: forall t m e. (IBTM' e t m)
                    => BoundStateIB t m
                    -> BoundStateIB t m
                    -> IBRWST m Bool
isBoundStateUpdated = undefined

-- | Potentially gets a forwarded var for a variable throwing an error if the
--   type is incorrect. Does not traverse to find the final element.
getForwardingVar :: forall t m e. (IBTM' e t m) => VarIB t m -> IBRWST m (Maybe (VarIB t m))
getForwardingVar v = getTermState v >>= \case
  (Forwarded tt tm i) -> matchType2 @t @m
     tt (throwInvalidTypeFound tt (typeRep @t))
     tm (throwInvalidTypeFound tm (typeRep @m))
     (\ HRefl HRefl -> pure $ Just i)
  _ -> pure Nothing


--  | Tries to get the error corresponding to a particular term.
--   Does not try to traverse the forwarding chain.
-- getTermError :: forall t m e. (IBTM' e t m) => VarIB t m -> IBRWST m (Maybe e)
-- getTermError v = getTermState v >>= \case
--  (Errored _ _ te i) -> matchType @e
--     te (throwInvalidTypeFound te (typeRep @e))
--     (\ HRefl -> pure $ Just i)
--  _ -> pure Nothing

-- | Finds the Representative element for a Var in our disjoint set structure.
--
--   Element returned should always be an Error or a Bound Term.
--   Forwards paths as needed.
getRepresentative :: forall t m e. (IBTM' e t m) => VarIB t m -> IBRWST m (VarIB t m)
getRepresentative v = whileGettingRepresentativeOf v $ getForwardingVar v >>= \case
  Nothing -> pure v
  Just v' -> do
    v'' <- getRepresentative v'
    when (v' /= v'') $ setTermState v (Forwarded typeRep typeRep v'')
    pure v''

instance (forall e. IBTM' e t m, Show (t (VarIB t m))) => MonadUnify t (IntBindT m) where

  unify :: VarIB t m -> VarIB t m -> IntBindT m (VarIB t m)
  unify a b = IntBindT $ unifyT a b

  -- equals :: VarIB t m -> VarIB t m -> IntBindT m Bool
  -- equals a b = IntBindT $ equalsT a b


-- | Unify two terms in IBRWST and return the resulting outcome.
unifyT :: forall t m e.  (IBTM' e t m)
       => VarIB t m -> VarIB t m -> IBRWST m (VarIB t m)
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
equalsT :: (IBTM' e t m) => VarIB t m -> VarIB t m -> IBRWST m Bool
equalsT a b
  | a == b = pure True
  | otherwise = undefined
    -- Check if unification or requality assumed -}

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

-- | Getting the latest version of a term, by updating all its member variables.
freshenTerm :: forall e t m. (IBTM' e t m)
              => t (VarIB t m)
              -> IBRWST m (t (VarIB t m))
freshenTerm = traverse getRepresentative

-- | If terms are functionally identical, merge them into a new entry.
equalizeTerms :: forall e t m. (IBTM' e t m)
              => t (VarIB t m)
              -> t (VarIB t m)
              -> IBRWST m (Maybe (t (VarIB t m)))
equalizeTerms ta tb = do
  ta' <- freshenTerm ta
  tb' <- freshenTerm tb
  pure $ if (not $ liftEq (==) ta' tb')
         then Just ta
         else Nothing

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
    matchTerms (Just ftv) (Just ttv) = equalizeTerms @e @t @m ftv ttv >>= \case
      Nothing ->  throwTermsNotUnified ftv ttv
      a -> pure a

    mergeRels :: TypeMap RelMap -> IBRWST m (TypeMap RelMap)
    mergeRels tr = TM.traverse mergeRelMap tr

    mergeRelMap :: forall p. (Typeable p) => Proxy p -> TypedVar -> IBRWST m TypedVar
    mergeRelMap proxy t@(TVar tt tm tv) = case TM.lookup proxy fr of
      Nothing -> pure t
      Just (TVar ft fm fv) -> mergeTypedVars tt tm ft fm tv fv

    -- You know what, this entire thing is a bit absurd, ensuring that
    -- three sets of terms all properly match. oh well.
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
  subsume a b = IntBindT $ subsumeT a b *> skip

  -- subsumes :: VarIB t m -> VarIB t m -> IntBindT m Bool
  -- subsumes = undefined
    -- Check structuralEquality
    -- check equality and unity assumptions
    -- check subsume assumptions
    -- check layer by layer subsumption.
       -- TODO :: unclear how to do.

-- | This just subsumes one term to another on a one off basis.
--
--   TODO :: Clean this up, it's too imperative.
subsumeT :: forall t m e. (IBTM' e t m) => VarIB t m -> VarIB t m -> IBRWST m (VarIB t m)
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
assumeSubsumed :: Monad m => VarIB t m -> VarIB t m -> IBRWST m Bool
assumeSubsumed v v' = do
  let pair = (flattenVID v, flattenVID v')
  res <- HS.member pair . subsumed . assumes <$> ask
  when res . tell $ mempty{subsumed=HS.singleton pair}
  pure res

-- | Checks whether a is marked as a subsumed term of b
hasSubsumed :: (IBTM' e t m) => VarIB t m -> VarIB t m -> IBRWST m Bool
hasSubsumed a b = do
  a' <- getRepresentative a
  b' :: VarIB t m <- getRepresentative b
  tis <- subsumedTerms <$> getBoundState a'
  let tl = IS.toList tis
  tl' <- traverse getRepresentative tl
  let tl'' = IS.fromList tl'
  modifyBoundState a' (\ s -> pure s{subsumedTerms=tl''})
  pure $ IS.member b' tl''

instance (Property p t t', IBTM' e t m, IBTM' e t' m)
       => MonadProperty p t t' (IntBindT m) where

  propertyOf :: VarIB t m -> IntBindT m (VarIB t' m)
  propertyOf v = IntBindT . whileGettingPropertyOf v (typeRep @p) $ do
    v' :: VarIB t m <- getRepresentative v
    tm :: TypeMap RelMap <- relations <$> getBoundState v'
    case TM.lookup (typeRep @p) tm of
      Nothing -> do
        nv :: VarIB t' m <- freeVarT
        modifyBoundState v' (\ b@BoundState{relations=rl} ->
              pure b{relations= TM.insert (typeRep @p) (tVar nv) rl})
        pure nv
      Just (TVar tt tm nv) -> matchType2 @t' @m
        tt (throwInvalidTypeFound tt (typeRep @t'))
        tm (throwInvalidTypeFound tm (typeRep @m))
        (\ HRefl HRefl -> pure nv)


instance (MonadError e (IntBindT m), MonadAttempt m) => MonadAttempt (IntBindT m) where

  attempt :: IntBindT m (Either f b) -> (f -> IntBindT m b) -> IntBindT m b
  attempt = defaultLiftAttempt
              (\ (a,s,w) -> (((),s,w),a))
              (\ (((),s,w), a) -> (a,s,w))

data Rule m a

type RuleTM t m = (
  Show (t (Var t (Rule m)))
  )

instance (MonadBind t m
         , RuleTM t m
         ) => MonadBind t (Rule m)

instance (MonadUnify t m
         , RuleTM t m
         ) => MonadUnify t (Rule m)

instance (MonadSubsume t m
         , RuleTM t m
         ) => MonadSubsume t (Rule m)

instance (MonadProperty p t t' m
         , RuleTM t m
         , RuleTM t' m
         ) => MonadProperty p t t' (Rule m)

class MonadRule m where

  addRule :: (MonadBind t m) => Var t m -> (Var t m -> Rule m ()) -> m ()

instance MonadRule (IntBindT m) where

  addRule v r = undefined


addRuleT :: ()
         => VarIB t m -> (VarIB t m -> Rule (IntBindT m) ()) -> IBRWST m ()
addRuleT = undefined

runRuleT :: ()
         => Rule (IntBindT m) () -> IBRWST m ()
runRuleT = undefined

liftAddRule :: (MonadTransControl mt, MonadRule m)
            => (Var t (mt m) -> Rule (mt m) ()) -> mt m ()
liftAddRule = undefined

-- | Foo (\ a -> (b :+$ c) <- match a
--               guard $ b == c
--               set a (2 :*$ b))
--
--  add the handler to all potential terms
--    -- It'll match on !e = !d + !f
--    --   Will fail since !d != !f
--    -- Match on !g = !h + !h
--    --   Will pass guard, match on !g (again, and run its payload?)
--    --   Nah -- Is a problem
