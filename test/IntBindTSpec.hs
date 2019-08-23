{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}

{-|
Module      : SudokuSpec
Description : Solves Sudoku by explicitly tracking ambiguity.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

-}

module IntBindTSpec where

import Intro hiding (Item)
import Hedgehog hiding (Var, Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Control.Concurrent.Supply
import Control.Monad.Morph
import Ivy.Prelude
import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.IntBindT
import Ivy.ErrorClasses
import Ivy.Testing

data ConstF a f where
  ConstF :: a -> ConstF a f

class EqIsh a where
  eqIsh :: a -> a -> Bool
  default eqIsh :: (Eq a) => a -> a -> Bool
  eqIsh = (==)

deriving instance (Show a) => Show (ConstF a f)
deriving instance Functor (ConstF a)
deriving instance Foldable (ConstF a)
deriving instance Traversable (ConstF a)

instance EqIsh Int

instance (EqIsh a) => Eq (ConstF a f) where
  (ConstF a) == (ConstF b) = eqIsh a b

instance (EqIsh a) => Eq1 (ConstF a) where
  liftEq _ (ConstF a) (ConstF b) = eqIsh a b

instance (EqIsh a, EqualityErr a e) => JoinSemiLattice1 e (ConstF a) where
  liftLatJoin (ConstF a) (ConstF b)
    | eqIsh a b = Right $ ConstF a
    | otherwise = Left $ valuesNotEqual a b

prt_free :: forall e m t. (MonadBind e m t) => PropertyT m ()
prt_free = do
  a :: Var m t <- freeVar
  b :: Var m t <- freeVar
  a /== b

hprop_free :: H.Property
hprop_free = mkProp $ prt_free @_ @_ @(ConstF Int)

prt_lookupFree :: forall e m t. (MonadBind e m t)
               => PropertyT m ()
prt_lookupFree = do
  v :: Var m t <- freeVar
  res <- lookupVar v
  assert $ isNothing res

hprop_lookupFree :: H.Property
hprop_lookupFree = mkProp $ prt_lookupFree @_ @_ @(ConstF Int)

prt_bind :: forall a e m. (MonadBind e m (ConstF a), EqIsh a, Show a)
         => Gen a -> PropertyT m ()
prt_bind gen = do
  v :: Var m (ConstF a) <- freeVar
  res <- lookupVar v
  assert $ isNothing res
  g <- forAll gen
  bindVar v (ConstF g)
  res' <- lookupVar v
  res' === Just (ConstF g)

hprop_bind :: H.Property
hprop_bind = mkProp $ prt_bind intGen

prt_rebind :: forall a e m. (MonadBind e m (ConstF a), EqIsh a, Show a)
           => Gen a -> PropertyT m ()
prt_rebind gen = do
  a <- ConstF <$> forAll gen
  b <- ConstF <$> forAll gen
  v <- newVar a
  lookupVar v >>= (=== Just a)
  v' <- bindVar v b
  lookupVar v  >>= (=== Just b)
  lookupVar v' >>= (=== Just b)

hprop_rebind :: H.Property
hprop_rebind = mkProp $ prt_rebind intGen

prt_redirect :: forall a e m. (MonadIO m, MonadBind e m (ConstF a), EqIsh a, Show a)
  => Gen a -> PropertyT m ()
prt_redirect gen = do
  a <- ConstF <$> forAll gen
  b <- ConstF <$> forAll gen
  va <- newVar a
  vb <- newVar b
  lookupVar va >>= (=== Just a)
  lookupVar vb >>= (=== Just b)
  vc <- redirectVar va vb
  lookupVar va >>= (=== Just b)
  lookupVar vb >>= (=== Just b)
  lookupVar vc >>= (=== Just b)

hprop_redirect :: H.Property
hprop_redirect = mkProp $ prt_redirect intGen

prt_freshen :: forall e m t. (MonadBind e m t)
            => PropertyT m ()
prt_freshen = do
  va :: Var m t <- freeVar
  vb :: Var m t <- freeVar
  va /== vb
  vc <- redirectVar va vb
  va' <- freshenVar va
  vb' <- freshenVar vb
  va' === vc
  vb' === vc

type BindM e = IntBindT (ExceptT e IO)

defaultConf :: Config
defaultConf = Config

mkProp :: PropertyT (BindM Text) () -> H.Property
mkProp = property . withBindM defaultConf

withBindM :: forall a e. (Show e) => Config -> PropertyT (BindM e) a -> PropertyT IO a
withBindM conf = hoist (morph2 . morph)

  where

    morph :: BindM e b -> ExceptT e IO b
    morph m = do
      supply <- liftIO newSupply
      (a, _, _) <- runIntBindT conf supply m
      pure a

    morph2 :: ExceptT e IO b -> IO b
    morph2 m = runExceptT m >>= \case
      Left  e -> panic $ show e
      Right a -> pure a

intGen :: Gen Int
intGen = Gen.int (Range.linear 0 20)


-- TODO :: Basic Test Cases to ensure that propagation, subsumption, and other
--         key operations are valid.
--
--   -- Terms :: Free, Lookup, Bind, Redirect, Freshen?
--   -- Properties
--   -- Rule
--   -- Default Rule
--   -- Equals
--   -- Unification
--   -- Subsumption
