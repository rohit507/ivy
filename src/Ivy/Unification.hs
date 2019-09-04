
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

module Ivy.Unification where

import Intro hiding (Item)
import Ivy.Prelude
import Algebra.Lattice
import Ivy.MonadClasses


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

    lookup = $lookupVar

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

    lookup = $lookupVar

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

    lookup = $lookupVar

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
