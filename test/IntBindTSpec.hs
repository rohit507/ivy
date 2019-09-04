
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
import Ivy.Unification
import Ivy.ErrorClasses
import Ivy.Testing ()
import Internal.IntBindT

newtype ConstF a f where
  ConstF :: a -> ConstF a f


class EqIsh a where
  eqIsh :: a -> a -> Bool
  default eqIsh :: (Eq a) => a -> a -> Bool
  eqIsh = (==)

deriving stock instance (Show a) => Show (ConstF a f)
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
  res <- $lookupVar v
  assert $ isNothing res

hprop_lookupFree :: H.Property
hprop_lookupFree = mkProp $ prt_lookupFree @_ @_ @(ConstF Int)

prt_bind :: forall a e m. (MonadBind e m (ConstF a), EqIsh a, Show a)
         => Gen a -> PropertyT m ()
prt_bind gen = do
  v :: Var m (ConstF a) <- freeVar
  res <- $lookupVar v
  assert $ isNothing res
  g <- forAll gen
  bindVar v (ConstF g)
  res' <- $lookupVar v
  res' === Just (ConstF g)

hprop_bind :: H.Property
hprop_bind = mkProp $ prt_bind intGen

prt_rebind :: forall a e m. (MonadBind e m (ConstF a), EqIsh a, Show a)
           => Gen a -> PropertyT m ()
prt_rebind gen = do
  a <- ConstF <$> forAll gen
  b <- ConstF <$> forAll gen
  v <- newVar a
  $lookupVar v >>= (=== Just a)
  v' <- bindVar v b
  $lookupVar v  >>= (=== Just b)
  $lookupVar v' >>= (=== Just b)

hprop_rebind :: H.Property
hprop_rebind = mkProp $ prt_rebind intGen

prt_redirect :: forall a e m. (MonadIO m, MonadBind e m (ConstF a), EqIsh a, Show a)
  => Gen a -> PropertyT m ()
prt_redirect gen = do
  a <- ConstF <$> forAll gen
  b <- ConstF <$> forAll gen
  va <- newVar a
  vb <- newVar b
  $lookupVar va >>= (=== Just a)
  $lookupVar vb >>= (=== Just b)
  vc <- redirectVar va vb
  $lookupVar va >>= (=== Just b)
  $lookupVar vb >>= (=== Just b)
  $lookupVar vc >>= (=== Just b)

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
  $lookupVar vp >>= (=== Nothing)
  vp' <- bindVar vp a
  vp'' <- (Prop @(ConstF a)) `propertyOf` v
  $lookupVar vp >>= (=== Just a)
  $lookupVar vp' >>= (=== Just a)
  $lookupVar vp'' >>= (=== Just a)

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
  $lookupVar vap >>= (=== Nothing)
  $lookupVar vbp >>= (=== Nothing)
  bindVar vbp c
  $lookupVar vap >>= (=== Nothing)
  $lookupVar vbp >>= (=== Just c)
  redirectVar va vb
  $lookupVar vap >>= (=== Just c)
  $lookupVar vbp >>= (=== Just c)

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
prt_singleRule gen = do
  -- traceM " ## Begin Test ## "
  a <- ConstF <$> forAll gen
  annotateShow a
  b <- ConstF <$> forAll gen
  annotateShow b
  va <- newVar a
  annotateShow va
  vp <- Prop @(ConstF a) `propertyOf` va
  annotateShow vp
  annotateShow =<< $lookupVar va
  annotateShow =<< $lookupVar vp
  lift . addRule $ $lookupVar va >>= \case
      Nothing -> panic "va should already be assigned"
      Just n -> do
        -- traceM $ "THIS IS N :" <> show n
        -- traceM $ "THIS IS N++ :" <> show (n + 1)
        vp <- Prop @(ConstF a) `propertyOf` va
        res <- bindVar vp (n + 1)
        -- traceM $ "THIS IS RES :" <> show res
        skip
  annotateShow =<< $lookupVar va
  annotateShow =<< $lookupVar vp
  $lookupVar va >>= (=== Just a)
  $lookupVar vp >>= (=== Just (a + 1))
  vc <- bindVar va b
  annotateShow vc
  annotateShow vp
  annotateShow =<< $lookupVar va
  annotateShow =<< $lookupVar vp
  $lookupVar va >>= (=== Just b)
  $lookupVar vp >>= (=== Just (b + 1))
  -- traceM " ## End Test ## "
  skip

hprop_singleRule :: H.Property
hprop_singleRule = mkProp $ prt_singleRule @Int @Text @(BindM Text) intGen


prt_sumProp :: forall a e m. ( Var m ~ Var (Rule m)
                            , MonadRule e m
                            , MonadRule e (Rule m)
                            , Alternative (Rule m)
                            , MonadFail (Rule m)
                            , MonadBind e (Rule m) (ConstF a)
                            , MonadBind e m (ConstF a)
                            , EqIsh a
                            , Show a
                            , Num a)
             => Gen a -> PropertyT m ()
prt_sumProp gen = do
  a <- ConstF <$> forAll gen
  annotateShow a
  b <- ConstF <$> forAll gen
  annotateShow b
  let s = a + b
  annotateShow s

  va <- freeVar
  vb <- freeVar
  vs <- freeVar

  annotateShow va
  annotateShow vb
  annotateShow vs

  lift . addRule $ sumPropRule @a @e @m va vb vs

  $lookupVar va >>= (=== Nothing)
  $lookupVar vb >>= (=== Nothing)
  $lookupVar vs >>= (=== Nothing)

  (forAll $ Gen.element @_ @String ["ab","as","bs"]) >>= \case
    "ab" -> do
      cover 20 "a and b" True
      _ <- bindVar va a
      _ <- bindVar vb b
      skip
    "as" -> do
      cover 20 "a and s" True
      _ <- bindVar va a
      _ <- bindVar vs s
      skip
    "bs" -> do
      cover 20 "b and s" True
      _ <- bindVar vb b
      _ <- bindVar vs s
      skip
    _ -> panic "unreachable"

  $lookupVar va >>= (=== Just a)
  $lookupVar vb >>= (=== Just b)
  $lookupVar vs >>= (=== Just s)

sumPropRule :: forall a e m. ( MonadRule e m
                            , Alternative (Rule m)
                            , MonadBind e (Rule m) (ConstF a)
                            , MonadFail (Rule m)
                            , Num a
                            )
  => Var m (ConstF a) -> Var m (ConstF a) -> Var m (ConstF a) -> Rule m ()
sumPropRule va vb vs
  = do
  forward va vb vs <|> backward va vb vs <|> backward vb va vs

  where

    forward va vb vs = do
      Just a <- $lookupVar va
      Just b <- $lookupVar vb
      _ <- bindVar vs (a + b)
      skip

    -- NOTE :: We do use lookup orders to explicitly differentiate rules,
    --        so for the moment you should make sure no alternatives
    backward va vb vs = do
      Just b <- $lookupVar vb
      Just s <- $lookupVar vs
      _ <- bindVar va (s - b)
      skip

hprop_sumProp :: H.Property
hprop_sumProp = mkProp $ prt_sumProp @Int @Text @(BindM Text) intGen
