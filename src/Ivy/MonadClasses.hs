{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.MonadClasses where

import Intro hiding (Item)
import Ivy.Prelude
import Algebra.Lattice
-- import qualified Data.Text as Text
-- import Data.HashSet (HashSet)
-- import qualified Data.HashSet as HS
-- import Ivy.Assertions

-- import Data.Monoid (All, getAll)

-- * These classes are components of a somewhat modified version of
--   `Control.Unification.BindingMonad` from `unification-fd`. It
--   still performs structural unification, but with a few key differences:
--
--     1) It doesn't choke on cyclic terms.
--     2) Provides a rollback mechanism that can still return information
--        from reverted branches of execution.
--     3) Triggers hooks when terms are unified.
--
--   All of these properties are desired if we want to use unification
--   as a significant part of a synthesis process, or as an element in the
--   analysis of inherently cyclic term graphs.
--
--   TODO :: Should we go back to being more explicit about the type of each
--           term in our graph, rather than definingn to be made is about whether we
--          split up the union-find and definitional layers or have them
--          both handled by a single monolith.
--
--          - The former should be more reusable, since we're squishing the
--            term level semantics of a bunch of things down flat.
--
--          - The latter would likely be faster and easier to optimize.
--            I suspect it would be faster to build, but not as simple
--            to manipulate.


-- | A context that is an instance of MonadBind can create variables that
--   represent single terms in a recursive expression, as well as rebind them
--   to new values, and declare that one variable should be redirected into
--   another.
class ( Typeable t
      , Typeable m
      , Traversable t
      , JoinSemiLattice1 e t
      , Eq1 t
      , Monad m
      , Show (Var m t)
      , Hashable (Var m t)
      , Ord (Var m t)
      , MonadError e m)
    => MonadBind (e :: Type) m t | m -> e where

  type Var m :: (Type -> Type) -> Type

  -- | Create a free variable with no term bound to it
  freeVar :: m (Var m t)

  -- | lookup the term for a variable, returns Nothing if the variable is free.
  lookupVar :: Var m t -> m (Maybe (t (Var m t)))

  -- | Binds the given term to a variable.
  bindVar   :: Var m t -> t (Var m t) -> m (Var m t)

  -- | Deletes the contents of the first variable, and makes all references to
  --   it instead point to second variable.
  redirectVar :: Var m t -> Var m t -> m (Var m t)

  -- | Does not modify the state of m at all, but returns the most up to date
  --   variable that is equivalent to the input.
  --
  --   Forall a b in Var m t
  --      unified a b === (==) <$> freshenVar a <*> freshenVar b
  --
  --   after two calls to freshen var, two terms should be unified only if they're
  freshenVar :: Var m t -> m (Var m t)

newVar :: (MonadBind e m t) => t (Var m t) -> m (Var m t)
newVar t = do
  v <- freeVar
  bindVar v t

-- | Properties are singleton types which reference some functional relation
--   between terms.
class (Typeable p, Typeable (From p), Typeable (To p)) => Property p where
  type From p :: Type -> Type
  type To   p :: Type -> Type

  rep :: p

class (Monad m, MonadBind e m (From p), MonadBind e m (To p), Property p) => MonadProperty e p m where

  -- | This will get the property related to the input term, generating a
  --   free term if it does not already exist.
  --
  --   Properties are many-to-one relationships between terms. For instance
  --   many terms can have the same type, but no term can have multiple
  --   types.
  propertyOf :: p -> Var m (From p) -> m (Var m (To p))

-- | This class is only relevant to implementers of a MonadProperty.
--   Basically, it gives us a way to traverse each of the potential
--   property pairs for some term, and appropriately handle them.
class MonadProperties e m where

  getPropertyPairs :: forall a t. (MonadBind e m t)
      => (forall proxy p. (From p ~ t
                         , MonadAssume e m (To p)
                         , MonadProperty e p m
                         , Property p)
                      => proxy p -> These (Var m (To p)) (Var m (To p)) -> m a)
      -> (a -> a -> m a)
      -> a
      -> Var m t -> Var m t -> m a

-- | This class is mostly only relevant to implementers of a MonadBind.
--   In effect we refactor the visited sets as assumptions that are held
--   during some part of the computation.
--
--   This basically makes it easier to handle coinductive reasoning about
--   equality, unity, and subsumption.
class (MonadBind e m t) => MonadAssume e m t where


  -- | Within the passed action assume the two variables are equivalent.
  assumeEqual :: Var m t -> Var m t -> m a -> m a

  -- | Within the passed action assume the two variables are unified.
  assumeUnified :: Var m t -> Var m t -> m a -> m a

  -- | Within the passed action assume that the first variable subsumes the
  --   second. .
  assumeSubsumed :: Var m t -> Var m t -> m a -> m a

  -- | set global state
  assertEqual :: Var m t -> Var m t -> m ()
  assertUnified :: Var m t -> Var m t -> m ()
  assertSubsumed :: Var m t -> Var m t -> m ()

  isAssumedEqual :: Var m t -> Var m t -> m Bool
  isAssumedUnified :: Var m t -> Var m t -> m Bool
  isAssumedSubsumed :: Var m t -> Var m t -> m Bool

-- | Rules allow for the enforcement of relationships between terms as an
--   operation is performed.
class ( forall g. (MonadBind     e m g) => MonadBind e (Rule m) g
      , forall k. (MonadAssume   e m k) => MonadAssume e (Rule m) k
      , forall p. (MonadProperty e p m) => MonadProperty e p (Rule m)
      , MonadError e m
      , GetErr (m)
      , GetErr (Rule m)
      , e ~ Err m
      , Err m ~ Err (Rule m)
      , MonadRule e (Rule m)
      , Rule (Rule m) ~ (Rule m)
      , Var m ~ Var (Rule m)
      ) => MonadRule e m | m -> e where

  type Rule m :: Type -> Type

  -- | Default implementation exists for r ~ m, where addRule is just identity.
  --   since any recursively defined rules should just become a single
  --   larger rule.
  addRule :: Rule m () -> m ()
  default addRule :: (Rule m ~ m) => Rule m () -> m ()
  addRule = id

type These2 a = These a a

data BinOpFuncs a b v e m t = BinOpFuncs
 { check :: These2 v -> m (Maybe a) -- ^ Do we need to recurse?
 , assume :: forall c. These2 v -> m c -> m c -- ^ modify all recursive steps
 , lookup :: v -> m (Maybe (t v)) -- ^ lookup term
 , handle :: e -> m b -- ^ Handle errors
 , merge  :: These2 v -> Maybe b -> m a -- ^ Merge terms given result of op
 , traversing :: forall d. (d -> m a) -> t d -> m b -- ^ custom traverse (w/ possible short-circuiting)
 }

recBinOp :: forall a b v e m t. (Show a, Show v, Monad m, Functor t, JoinSemiLattice1 e t)
         => BinOpFuncs a b v e m t
         -> These v v
         -> m a
recBinOp BinOpFuncs{..} = fix $ \ recurse inputs -> do
  -- traceM $ "recBinOp : " <> show inputs
  r <- check inputs
  -- traceM $ "checkResult : " <> show r
  case r of
    Just a -> do
      -- traceM $ "no rec : " <> show a
      pure a
    Nothing -> do
      -- traceM $ "rec : " <> show inputs
      subterm :: Maybe b <- assume inputs $ do
        (crushThese <$> bitraverse lookup lookup inputs) >>= \case
          Nothing -> pure Nothing
          Just (This ta) -> do
            -- traceM $ "this :" <> show inputs
            Just <$> traversing recurse (This <$> ta)
          Just (That tb) -> do
            -- traceM $ "that :" <> show inputs
            Just <$> traversing recurse (That <$> tb)
          Just (These ta tb) -> do
            -- traceM $ "these : " <> show inputs
            Just <$> case liftLatJoin ta tb of
              Left e -> handle e
              Right tu -> traversing recurse tu
      -- traceM "pre-merge"
      res <- merge inputs subterm
      -- traceM "post-merge"
      pure res

-- | Returns nothing if the terms aren't equal, otherwise it returns a list
--   of terms that should be unified to unify the input terms.
equals :: forall e m t. (MonadAssume e m t
                       , MonadProperties e m
                       , JoinSemiLattice1 e t
                       )
   => Var m t -> Var m t -> m Bool
equals a b = recBinOp fns (These a b)

  where

    fns :: BinOpFuncs Bool Bool (Var m t) e m t
    fns = BinOpFuncs{..}

    lookup = lookupVar

    traversing :: forall c. (c -> m Bool) -> t c -> m Bool
    traversing f t = allM f $ foldToList t

    check :: These2 (Var m t) -> m (Maybe Bool)
    check (These a b) = do
      -- traceM $ "checking : " <> show a <> show b
      ifM (a `isAssumedEqual` b) (pure $ Just True) (pure $ Nothing)
    check _ = do
      -- traceM $ "no check : " <>  show v
      pure $ Just True

    assume :: forall c. These2 (Var m t) -> m c -> m c
    assume (These a b) = assumeEqual a b
    assume _ = id

    handle :: e -> m Bool
    handle _ = pure $ False

    merge :: These2 (Var m t) -> Maybe Bool -> m Bool
    merge (This _) eq = pure $ fromMaybe True eq
    merge (That _) eq = pure $ fromMaybe True eq
    merge (These a b) eq = (pure $ fromMaybe True eq) &&^ equalsProps a b

    equalsProps :: Var m t -> Var m t -> m Bool
    equalsProps a b = helper a b

    helper a b = getPropertyPairs @e getEq (\ a b -> pure $ a && b) True a b
      where
        getEq :: forall p proxy. (From p ~ t, MonadAssume e m (To p))
                 => proxy p -> These (Var m (To p)) (Var m (To p)) -> m Bool
        getEq _ (These a b) = equals a b
        getEq _ _ = pure True

-- | unifies two terms as needed
unify :: forall e m t. ( MonadAssume e m t
                      , MonadProperties e m
                      )
   => Var m t -> Var m t -> m (Var m t)
unify a b = do
  -- traceM "u1"
  recBinOp fns (These a b)

   where

    fns :: BinOpFuncs (Var m t) (t (Var m t)) (Var m t) e m t
    fns = BinOpFuncs{..}

    lookup = lookupVar

    check :: These2 (Var m t) -> m (Maybe (Var m t))
    check (This a) = do
      -- traceM $ "uni Check This."
      pure $ Just a
    check (That b) = do
      -- traceM $ "uni Check That."
      pure $ Just b
    check (These a b) = do
      -- traceM $ "uni Check These."
      res <- ifM (a `isAssumedUnified` b) (pure . Just $ b) (pure Nothing)
      -- traceM $ "uni Check result : " <> show res
      pure res

    assume :: forall c. These2 (Var m t) -> m c -> m c
    assume (These a b) = assumeUnified @e @m a b
    assume _ = id

    handle :: e -> m b
    handle = throwError

    traversing :: forall c. (c -> m (Var m t)) -> t c -> m (t (Var m t))
    traversing = traverse

    merge (These a b) mTerm = do
      -- traceM "merge 1"
      unifyProps a b
      -- traceM "merge 2"
      b' <- maybe (pure b) (bindVar b) mTerm
      -- traceM "merge 3"
      redirectVar a b'
      -- traceM "merge 4"
      assertUnified a b
      -- traceM "merge 5"
      pure b'
    merge _ _ = panic "unreachable"

    unifyProps :: Var m t -> Var m t -> m ()
    unifyProps a b = getPropertyPairs unifyProp (\ a b -> pure $ a <> b) mempty a b
      where
        unifyProp :: forall p proxy. (From p ~ t
                                    , MonadAssume e m (To p)
                                    , MonadProperty e p m
                                    , Property p)
                 => proxy p -> These (Var m (To p)) (Var m (To p)) -> m ()
        unifyProp _ (These a' b') = do
          -- traceM $ "UnifyProp these"
          unify @e @m @(To p) a' b' *> skip
        unifyProp _ (This a') = do
          -- traceM "UnifyProp this"
          (unify a' =<< ((rep :: p) `propertyOf` b)) *> skip
        unifyProp _ _ = do
          -- traceM "unifyProp that"
          skip

-- | Subsumes the first term to the second, returns the second.
--
--   FIXME :: This has a subtle error because we don't actually keep a visible
--           mapping from subsumed to subsumer. It'll end up duplicating terms
--           from the subsumer if they're referenced multiple times.
subsume :: forall e m t. ( MonadAssume e m t
                        , MonadAssume e (Rule m) t
                        , MonadRule e m
                        , MonadProperties e m
                        , MonadProperties e (Rule m)
                        ) => Var m t -> Var m t -> m (Var m t)
subsume a b = do
  -- traceM $ "start subsume : " <> show (a,b)
  reverseSub <- (b `isAssumedSubsumed` a)
  -- traceM "s1"
  sub <- a `isAssumedSubsumed` b
  -- traceM "s2"
  isUni <- a `isAssumedUnified` b
  -- traceM "s3"
  if
    | reverseSub && not isUni -> do
        -- traceM "su"
        unify a b
    | sub || isUni -> do
        -- traceM "sf"
        freshenVar b
    | otherwise -> do
        -- traceM "ss"
        (addRule $ performSubsume a b *> skip) *> freshenVar b

  where

    -- performSubsume :: Var m t -> Var m t -> Rule m (Var m t)
    performSubsume a b = do
      -- traceM $ "subsuming :" <> show a <> show b
      recBinOp fns (These a b)

    fns :: BinOpFuncs (Var m t) (t (Var m t)) (Var m t) e (Rule m) t
    fns = BinOpFuncs{..}

    lookup = lookupVar

    -- check :: These (Var m t) (Var m t) -> Rule m (Maybe (Var m t))
    check (This a) = do
      -- traceM "check this"
      Just <$> (performSubsume a =<< freeVar)
    check (That b) = do
      -- traceM "check that"
      pure $ Just b
    -- Even if a does already subsume b we still need to run the recursive
    -- pass of the rule, since it will update the subsumed term anyway
    -- The only other case occours when two terms subsume each other and
    -- need to be unified.
    check (These a b) = do
      -- traceM $ "check these : " <> show (a,b)
      reverseSub <- b `isAssumedSubsumed` a
      sub        <- a `isAssumedSubsumed` b
      isUni      <- a `isAssumedUnified`  b
      r <- if
        | reverseSub && not isUni -> Just <$> unify a b
        | sub || isUni -> pure $ Just b
        | otherwise -> pure Nothing
      -- traceM $ "result : " <> show r
      pure r

    assume :: forall c. These (Var m t) (Var m t) -> Rule m c -> Rule m c
    assume (These a b) = -- trace "assuming" $
      assumeSubsumed a b
    assume _ = id

    handle ::e -> Rule m c
    handle = throwError

    traversing = traverse -- (trace "f" $ f)

    merge :: These (Var m t) (Var m t) -> Maybe (t (Var m t)) -> Rule m (Var m t)
    merge (These a b) mTerm = do
      -- traceM $ "merging : " <> show a <> show b
      assertSubsumed a b
      maybe (pure b) (bindVar b) mTerm

    merge _ _ = panic "unreachable"
