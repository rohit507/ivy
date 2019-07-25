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

module Ivy.MonadClasses
  ( MonadBind(..)
  , Property
  , MonadProperty(..)
  , MonadProperties(..)
  , MonadAssume(..)
  , MonadRule(..)
  , equals
  , unify
  , subsume
  ) where

import Ivy.Prelude
import Algebra.Lattice
import qualified Data.Text as Text
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS

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

class ( Typeable t
      , Traversable t
      , Monad m
      , Hashable (Var m t)
      , Eq (Var m t)
      , MonadError e m)
    => MonadBind (e :: Type) t m | m -> e where

  type Var m :: (Type -> Type) -> Type

  freeVar :: m (Var m t)

  lookupVar :: Var m t -> m (Maybe (t (Var m t)))

  bindVar   :: Var m t -> t (Var m t) -> m (Var m t)

  -- Makes the first variable point to the second.
  redirectVar :: Var m t -> Var m t -> m (Var m t)

class Property p t t' | p -> t, p -> t'

class (Typeable p) => MonadProperty e p m where

  propertyOf :: (MonadBind e t m, MonadBind e t' m, Property p t t')
      => p -> Var m t -> m (Var m t')

class MonadProperties e m where

  getOverlappingProperties :: forall a t. (Monoid a, MonadBind e t m)
      => (forall t' . ( JoinSemiLattice1 e t'
                      , MonadAssume e t' m)
                      => Var m t' -> Var m t' -> m a)
      -> Var m t -> Var m t -> m a

class (MonadBind e t m) => MonadAssume e t m where

  -- Single Layer Equality
  isEqualTo :: Var m t -> Var m t -> m Bool

  assumeEqual :: Var m t -> Var m t -> m a -> m a

  -- Single Layer Unification
  isUnifiedWith :: Var m t -> Var m t -> m Bool

  assumeUnified :: Var m t -> Var m t -> m a -> m a

  -- Single Layer Subsumption
  isSubsumedBy :: Var m t -> Var m t -> m Bool

  assumeSubsumed :: Var m t -> Var m t -> m a -> m a

class ( forall t. (MonadBind e t m) => MonadBind e t r
      , forall t. (MonadAssume e t m) => MonadAssume e t r
      , forall p. (MonadProperty e p m) => MonadProperty e p r
      , Var m ~ Var r
      ) => MonadRule e r m | m -> e, m -> r, r -> e where

  addRule :: r a -> m ()


data BinOpContext a b e t m = BinOpContext
  { check :: These (Var m t) (Var m t) -> m (Maybe a)
  , assume :: These (Var m t) (Var m t) -> m (Maybe b) -> m (Maybe b)
  , handle :: e -> m b
  , collapse :: t a -> m b
  , merge :: These (Var m t) (Var m t) -> Maybe b -> m a
  }

recBinOpF :: forall a b e t m. (MonadBind e t m, JoinSemiLattice1 e t)
         => BinOpContext a b e t m
         -> (These (Var m t) (Var m t) -> m a)
         -> These (Var m t) (Var m t)
         -> m a
recBinOpF BinOpContext{..} = \ recurse inputs ->
  flip maybeM (check inputs) $ do
    subterm :: Maybe b <- assume inputs $
        bitraverseThese (lookupVar @e) (lookupVar @e) inputs >>= \case
        --
        This Nothing   -> nothingCase
        This (Just ta) -> thisCase recurse ta
        --
        That Nothing   -> nothingCase
        That (Just tb) -> thatCase recurse tb
        --
        These Nothing   Nothing   -> nothingCase
        These (Just ta) Nothing   -> thisCase recurse ta
        These Nothing   (Just tb) -> thatCase recurse tb
        These (Just ta) (Just tb) -> theseCase recurse ta tb
    merge inputs subterm

  where


    nothingCase = pure Nothing
    thisCase f ta = Just <$> (collapse =<< traverse (f . This) ta)
    thatCase f tb = Just <$> (collapse =<< traverse (f . That) tb)
    theseCase f ta tb = Just <$> case liftLatJoin ta tb of
      Left e -> handle e
      Right tu -> collapse =<< traverse f tu

recBinOp :: forall a b e t m. (MonadBind e t m, JoinSemiLattice1 e t)
         => BinOpContext a b e t m
         -> These (Var m t) (Var m t)
         -> m a
recBinOp c = fix (recBinOpF c)

type OpSet m = HashSet (TVar m, TVar m)

data TVar m where
  TVar :: (MonadBind e t m) => TypeRep t -> Var m t -> TVar m

instance Hashable (TVar m) where
  hashWithSalt s (TVar _ v) = hashWithSalt s v

instance Eq (TVar m) where
  (TVar t v) == (TVar t' v') = fromMaybe False $ do
    HRefl <- eqTypeRep t t'
    pure (v == v')

-- | Returns nothing if the terms aren't equal, otherwise it returns a list
--   of terms that should be unified to unify the input terms.
equals :: forall e t m. (MonadAssume e t m, MonadProperties e m, JoinSemiLattice1 e t)
   => Var m t -> Var m t -> m (Maybe (OpSet m))
equals a b = recBinOp context (These a b)

  where

    context :: BinOpContext (Maybe (OpSet m)) (Maybe (OpSet m)) e t m
    context = BinOpContext{..}

    check (These a b) = ifM (a `isEqualTo` b)
       (pure . Just $ Just mempty) (pure Nothing)
    check _ = pure . Just $ Just mempty

    assume (These a b) = assumeEqual a b
    assume _ = id

    handle _ = pure $ Nothing

    collapse term = pure $ foldr mappendMaybe (Just mempty) term

    merge (This _) meq = pure $ join meq
    merge (That _) meq = pure $ join meq
    merge (These a b) meq = do
      let eqs = mappendMaybe (Just $ HS.singleton (TVar typeRep a, TVar typeRep b)) (join meq)
      (`mappendMaybe` eqs) <$> equalsProps a b


    equalsProps :: Var m t -> Var m t -> m (Maybe (OpSet m))
    equalsProps a b = mappendMaybes <$> helper a b

    helper a b = getOverlappingProperties @e (getOpSet) a b

    getOpSet :: forall t'. (JoinSemiLattice1 e t', MonadAssume e t' m)
                 => Var m t' -> Var m t' -> m [Maybe (OpSet m)]
    getOpSet a b = pure <$> equals @e @t' @m a b


-- | unifies two terms as needed
unify :: forall e t m. (MonadAssume e t m, MonadProperties e m, JoinSemiLattice1 e t)
   => Var m t -> Var m t -> m (Var m t)
unify a b = recBinOp context (These a b)

  where

    context :: BinOpContext (Var m t) (t (Var m t)) e t m
    context = BinOpContext{..}

    check (This a) = pure $ Just a
    check (That b) = pure $ Just b
    check (These a b) = ifM (a `isUnifiedWith` b)
       (pure . Just $ b) (pure Nothing)


    assume (These a b) = assumeUnified a b
    assume _ = id

    handle = throwError

    collapse = pure

    merge (These a b) mTerm = do
      unifyProps a b
      b' <- maybe (pure b) (bindVar b) mTerm
      redirectVar a b'
    merge _ _ = panic "unreachable"

    unifyProps :: Var m t -> Var m t -> m ()
    unifyProps a b = getOverlappingProperties @e unifyProp a b

    unifyProp :: forall t'. (JoinSemiLattice1 e t', MonadAssume e t' m)
                 => Var m t' -> Var m t' -> m ()
    unifyProp a b = unify @e @t' @m a b *> skip


subsume' :: forall e t r. ( MonadRule e r r
                         , MonadAssume e t r
                         , JoinSemiLattice1 e t)
        => Var r t -> Var r t -> r (Var r t)
subsume' = subsume

-- | Subsumes the first term to the second, returns the second.
subsume :: forall e t r m. ( MonadRule e r m
                          , MonadBind e t m
                          , MonadBind e t r
                          , MonadAssume e t r
                          , JoinSemiLattice1 e t
                          , Var r ~ Var m)
        => Var r t -> Var r t -> m (Var r t)
subsume a b = (addRule $ performSubsume a b) *> pure b

  where

    performSubsume :: Var r t -> Var r t -> r (Var r t)
    performSubsume a b = recBinOp context (These a b)

    context :: BinOpContext (Var r t) (t (Var r t)) e t r
    context = BinOpContext{..}

    check :: These (Var r t) (Var r t) -> r (Maybe (Var r t))
    check (This a) = Just <$> (performSubsume a =<< freeVar)
    check (That b) = pure $ Just b
    -- Even if a does subsume b, then we must assume that
    check (These a b) = pure Nothing


    assume :: forall c. These (Var r t) (Var r t) -> r c -> r c
    assume (These a b) = assumeSubsumed a b
    assume _ = id

    handle :: forall c. e -> r c
    handle = throwError

    collapse :: t (Var r t) -> r (t (Var r t))
    collapse = pure

    merge :: These (Var r t) (Var r t) -> Maybe (t (Var r t)) -> r (Var r t)
    merge (These a b) mTerm = maybe (pure b) (bindVar b) mTerm
    merge _ _ = panic "unreachable"
