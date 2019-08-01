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

import Ivy.Prelude
import Algebra.Lattice
import qualified Data.Text as Text
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS

import Data.Monoid (All, getAll)

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
      , Traversable t
      , Monad m
      , Hashable (Var m t)
      , Eq (Var m t)
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

-- | Properties are singleton types which reference some functional relation
--   between terms.
class (Typeable p) => Property p t t' | p -> t, p -> t'

class (Typeable p) => MonadProperty e p m where

  -- | This will get the property related to the input term, generating a
  --   free term if it does not already exist.
  --
  --   Properties are many-to-one relationships between terms. For instance
  --   many terms can have the same type, but no term can have multiple
  --   types.
  propertyOf :: (MonadBind e m t, MonadBind e m t', Property p t t')
      => p -> Var m t -> m (Var m t')


class (MonadBind e m t) => MonadUnify e m t where

  -- | Check whether two terms are equal. i.e That they could be unified without
  --   an error.
  --
  --   NOTE :: This should be aware of assumptions
  equals :: Var m t -> Var m t -> m Bool
  default equals :: (MonadAssume e m t) => Var m t -> Var m t -> m Bool
  equals = undefined

  -- | Unify two terms and return the variable for the result. Once run
  --   both inputs and the return value are all functionally identical.
  --
  --   NOTE :: This also unifies the properties of both variables.
  unify :: Var m t -> Var m t -> m (Var m t)
  default unify :: (MonadAssume e m t) => Var m t -> Var m t -> m (Var m t)
  unify = undefined

  -- | Ensure that the first term subsumes the second.
  --
  --   NOTE :: This does not ensure that the properties all also subsume each
  --           other. There is no need, since the inputs stay separate.
  subsume :: Var m t -> Var m t -> m (Var m t)
  default subsume :: (MonadAssume e m t, MonadRule e m) => Var m t -> Var m t -> m (Var m t)
  subsume = undefined


-- | This class is only relevant to implementers of a MonadProperty.
--   Basically, it gives us a way to traverse each of the potential
--   property pairs for some term, and appropriately handle them.
class MonadProperties e m where

  getPropertyPairs :: forall a t. (MonadBind e m t)
      => (forall t' p proxy. ( MonadProperty e p m
                        , Property p t t')
                      => proxy p -> These (Var m t') (Var m t') -> m a)
      -> (a -> a -> m a)
      -> a
      -> Var m t -> Var m t -> m a

-- | This class is mostly only relevant to implementers of a MonadBind.
--   In effect we refactor the visited sets as assumptions that are held
--   during some part of the computation.
--
--   This basically makes it easier to handle coinductive reasoning about
--   equality, unity, and subsumption.
class (MonadUnify e m t) => MonadAssume e m t where

  -- | Are the two terms equal
  isAssumedEqual :: Var m t -> Var m t -> m Bool

  -- | Within the passed action assume the two variables are equivalent.
  assumeEqual :: Var m t -> Var m t -> m a -> m a

  -- | Variable equality that is aware of assumptions
  isAssumedUnified :: Var m t -> Var m t -> m Bool

  -- | Within the passed action assume the two variables are unified.
  assumeUnified :: Var m t -> Var m t -> m a -> m a

  -- | Single layer term subsumption, that is aware of assumptions
  isAssumedSubsumed :: Var m t -> Var m t -> m Bool

  -- | Within the passed action assume that the first variable subsumes the
  --   second. .
  assumeSubsumed :: Var m t -> Var m t -> m a -> m a

-- | Rules allow for the enforcement of relationships between terms as an
--   operation is performed.
class ( forall t. (MonadBind e m t) => MonadBind e (Rule m) t
      , forall t. (MonadUnify e m t) => MonadUnify e (Rule m) t
      , forall t. (MonadAssume e m t) => MonadAssume e (Rule m) t
      , forall p. (MonadProperty e p m) => MonadProperty e p (Rule m)
      , Var m ~ Var (Rule m)
      , Rule (Rule m) ~ (Rule m)
      ) => MonadRule e m | m -> e where

  type Rule m :: Type -> Type

  -- | Default implementation exists for r ~ m, where addRule is just identity.
  --   since any recursively defined rules should just become a single
  --   larger rule.
  addRule :: Rule m () -> m ()
  default addRule :: (Rule m ~ m) => Rule m () -> m ()
  addRule = id


data BinOpContext a b e m t = BinOpContext
  { check :: These (Var m t) (Var m t) -> m (Maybe a)
  , assume :: These (Var m t) (Var m t) -> m (Maybe b) -> m (Maybe b)
  , handle :: e -> m b
  , traversing :: forall c. (c -> m a) -> t c -> m b
  , merge :: These (Var m t) (Var m t) -> Maybe b -> m a
  }

{-
recBinOpF :: forall a b e m t. (MonadBind e m t, JoinSemiLattice1 e t)
         => BinOpContext a b e m t
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

    thisCase :: (These (Var m t) (Var m t) -> m a) -> t (Var m t) -> m (Maybe b)
    thisCase f ta = Just <$> (traversing f $ map This ta)


    thatCase :: (These (Var m t) (Var m t) -> m a) -> t (Var m t) -> m (Maybe b)
    thatCase f tb = Just <$> (traversing f $ map That tb)

    theseCase :: (These (Var m t) (Var m t) -> m a) -> t (Var m t) -> t (Var m t) -> m (Maybe b)
    theseCase f ta tb = Just <$> case liftLatJoin ta tb of
      Left e -> handle e
      Right tu -> traversing f tu

recBinOp :: forall a b e m t. (MonadBind e m t, JoinSemiLattice1 e t)
         => BinOpContext a b e m t
         -> These (Var m t) (Var m t)
         -> m a
recBinOp c = fix (recBinOpF c)

type OpSet m = HashSet (TVar m, TVar m)

data TVar m where
  TVar :: (MonadBind e m t) => TypeRep t -> Var m t -> TVar m

instance Hashable (TVar m) where
  hashWithSalt s (TVar _ v) = hashWithSalt s v

instance Eq (TVar m) where
  (TVar t v) == (TVar t' v') = fromMaybe False $ do
    HRefl <- eqTypeRep t t'
    pure (v == v')

-- | Returns nothing if the terms aren't equal, otherwise it returns a list
--   of terms that should be unified to unify the input terms.
defaultEquals :: forall e m t. (MonadAssume e m t, MonadProperties e m, JoinSemiLattice1 e t)
   => Var m t -> Var m t -> m Bool
defaultEquals a b = recBinOp context (These a b)

  where

    context :: BinOpContext Bool Bool e m t
    context = BinOpContext{..}

    traversing :: forall c. (c -> m Bool) -> t c -> m Bool
    traversing f t = allM f $ (foldMap (:[]) t :: [c])

    check (These a b) = ifM undefined -- (a `equals` b)
      (pure . Just $ True) (pure Nothing)
    check _ = pure . Just $ True

    assume (These a b) = assumeEqual a b
    assume _ = id

    handle _ = pure $ False

    merge (This _) eq = pure $ fromMaybe True eq
    merge (That _) eq = pure $ fromMaybe True eq
    merge (These a b) eq = (pure $ fromMaybe True eq) &&^ equalsProps a b

    equalsProps :: Var m t -> Var m t -> m Bool
    equalsProps a b = helper a b

    helper a b = getPropertyPairs @e getEq (&&^) True a b
      where
        getEq :: forall p t'. (JoinSemiLattice1 e t', MonadAssume e t' m)
                 => p -> These (Var m t') (Var m t') -> m Bool
        getEq _ (These a b) = equals a b
        getEq _ _ = pure True

-- | unifies two terms as needed
defaultUnify :: forall e m t. (MonadAssume e m t, MonadProperties e m, JoinSemiLattice1 e t)
   => Var m t -> Var m t -> m (Var m t)
defaultUnify a b = recBinOp context (These a b)

  where

    context :: BinOpContext (Var m t) (t (Var m t)) e m t
    context = BinOpContext{..}

    check (This a) = pure $ Just a
    check (That b) = pure $ Just b
    check (These a b) = ifM undefined -- (a `isUnifiedWith` b)
       (pure . Just $ b) (pure Nothing)


    assume (These a b) = assumeUnified a b
    assume _ = id

    handle = throwError

    traversing = traverse

    merge (These a b) mTerm = do
      unifyProps a b
      b' <- maybe (pure b) (bindVar b) mTerm
      redirectVar a b'
    merge _ _ = panic "unreachable"

    unifyProps :: Var m t -> Var m t -> m ()
    unifyProps a b = getPropertyPairs unifyProp (*>) mempty a b
      where
        unifyProp :: forall p t'. (MonadProperty e p m
                                 , Property p t t'
                                 , JoinSemiLattice1 e t'
                                 , MonadAssume e t' m)
                 => p -> These (Var m t') (Var m t') -> m ()
        unifyProp _ (These a' b') = unify @e @t' @m a' b' *> skip
        unifyProp p (This a') = (unify a' =<< (p  `propertyOf` b)) *> skip
        unifyProp _ _ = skip

-- | Subsumes the first term to the second, returns the second.
--
--   FIXME :: This has a subtle error because we don't actually keep a visible
--           mapping from subsumed to subsumer. It'll end up duplicating terms
--           from the subsumer if they're referenced multiple times.
defaultSubsume :: forall e t r m. ( MonadRule e r m
                          , MonadBind e m t
                          , MonadBind e t r
                          , MonadAssume e t r
                          , JoinSemiLattice1 e t
                          , Var r ~ Var m)
        => Var r t -> Var r t -> m (Var r t)
defaultSubsume a b = (addRule $ performSubsume a b) *> pure b

  where

    performSubsume :: Var r t -> Var r t -> r (Var r t)
    performSubsume a b = recBinOp context (These a b)

    context :: BinOpContext (Var r t) (t (Var r t)) e t r
    context = BinOpContext{..}

    check :: These (Var r t) (Var r t) -> r (Maybe (Var r t))
    check (This a) = Just <$> (subsume a =<< freeVar)
    check (That b) = pure $ Just b
    -- Even if a does already subsume b we still need to run the recursive
    -- pass of the rule, since it will update the subsumed term anyway
    -- The only other case occours when two terms subsume each other and
    -- need to be unified.
    check (These a b) = ifM undefined --(b `isSubsuming` a)
                            (Just <$> unify a b)
                            (pure Nothing)

    assume :: forall c. These (Var r t) (Var r t) -> r c -> r c
    assume (These a b) = assumeSubsumed a b
    assume _ = id

    handle :: forall c. e -> r c
    handle = throwError

    traversing = traverse

    merge :: These (Var r t) (Var r t) -> Maybe (t (Var r t)) -> r (Var r t)
    merge (These _ b) mTerm = maybe (pure b) (bindVar b) mTerm
    merge _ _ = panic "unreachable"
-}
