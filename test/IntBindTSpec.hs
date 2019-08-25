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
import Ivy.Testing ()

newtype ConstF a f where
  ConstF :: a -> ConstF a f

class EqIsh a where
  eqIsh :: a -> a -> Bool
  default eqIsh :: (Eq a) => a -> a -> Bool
  eqIsh = (==)

deriving instance (Show a) => Show (ConstF a f)
deriving instance Functor (ConstF a)
deriving instance Foldable (ConstF a)
deriving instance Traversable (ConstF a)
deriving newtype instance Num a => Num (ConstF a f)

instance EqIsh Int

instance (EqIsh a) => Eq (ConstF a f) where
  (ConstF a) == (ConstF b) = eqIsh a b

instance (EqIsh a) => Eq1 (ConstF a) where
  liftEq _ (ConstF a) (ConstF b) = eqIsh a b

instance (EqIsh a, EqualityErr e a) => JoinSemiLattice1 e (ConstF a) where
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

hprop_freshen :: H.Property
hprop_freshen = mkProp $ prt_freshen @_ @_ @(ConstF Int)

data Prop (t :: Type -> Type) = Prop

instance (Typeable t, Typeable (Prop t)) => Property (Prop t) where
  type From (Prop t) = t
  type To   (Prop t) = t
  rep = Prop

prt_property :: forall a e m. (MonadProperty e (Prop (ConstF a)) m, MonadBind e m (ConstF a), EqIsh a, Show a)
             => Gen a -> PropertyT m ()
prt_property gen = do
  a <- ConstF <$> forAll gen
  v <- freeVar
  vp :: Var m (ConstF a) <- (Prop @(ConstF a)) `propertyOf` v
  lookupVar vp >>= (=== Nothing)
  vp' <- bindVar vp a
  vp'' <- (Prop @(ConstF a)) `propertyOf` v
  lookupVar vp >>= (=== Just a)
  lookupVar vp' >>= (=== Just a)
  lookupVar vp'' >>= (=== Just a)

hprop_property :: H.Property
hprop_property = mkProp $ prt_property intGen


prt_propertyRedirect :: forall a e m. (MonadProperty e (Prop (ConstF a)) m
                                     , MonadBind e m (ConstF a)
                                     , EqIsh a
                                     , Show a)
             => Gen a -> PropertyT m ()
prt_propertyRedirect gen = do
  c <- ConstF <$> forAll gen
  va <- freeVar
  annotateShow va
  vb <- freeVar
  annotateShow vb
  vap <- (Prop @(ConstF a)) `propertyOf` va
  annotateShow vap
  vbp <- (Prop @(ConstF a)) `propertyOf` vb
  annotateShow vbp
  lookupVar vap >>= (=== Nothing)
  lookupVar vbp >>= (=== Nothing)
  bindVar vbp c
  lookupVar vap >>= (=== Nothing)
  lookupVar vbp >>= (=== Just c)
  redirectVar va vb
  lookupVar vap >>= (=== Just c)
  lookupVar vbp >>= (=== Just c)

hprop_propertyRedirect :: H.Property
hprop_propertyRedirect = mkProp $ prt_propertyRedirect intGen

prt_singleRule :: forall a e m. ( MonadProperty e (Prop (ConstF a)) m
                               , MonadProperty e (Prop (ConstF a)) (Rule m)
                               , EqualityErr e a
                               , MonadRule e m
                               , MonadRule e (Rule m)
                               , EqIsh a
                               , Show a
                               , Num a)
             => Gen a -> PropertyT m ()
-- prt_singleRule gen = undefined
prt_singleRule gen = do
  a <- ConstF <$> forAll gen
  b <- ConstF <$> forAll gen
  va <- newVar a
  vp <- Prop @(ConstF a) `propertyOf` va
  lift . addRule $ ((lookupVar va >>= \case
      Nothing -> skip
      Just n -> do
        vp <- Prop @(ConstF a) `propertyOf` va
        bindVar vp (n + 1)
        skip) :: Rule m ())
  lookupVar va >>= (=== Just a)
  lookupVar vp >>= (=== Just (a + 1))
  bindVar va b
  lookupVar va >>= (=== Just b)
  lookupVar vp >>= (=== Just (b + 1))

hprop_singleRule :: H.Property
hprop_singleRule = mkProp $ prt_singleRule @Int @Text @(BindM Text) intGen





-- rules
-- default rules?
-- unify
-- equals
-- subsume

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
