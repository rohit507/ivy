
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : SudokuSpec
Description : Solves Sudoku by explicitly tracking ambiguity.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

-}

module HuttonSpec where

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

deriving stock instance (Show a) => Show (ConstF a f)
deriving instance Functor (ConstF a)
deriving instance Foldable (ConstF a)
deriving instance Traversable (ConstF a)
deriving newtype instance Num a => Num (ConstF a f)

deriving newtype instance (Eq a) => Eq (ConstF a f)

instance (Eq a, EqualityErr e a) => JoinSemiLattice1 e (ConstF a) where
  liftLatJoin (ConstF a) (ConstF b)
    | a == b = Right $ ConstF a
    | otherwise = Left $ valuesNotEqual a b

newtype MinF a f where
  MinF :: a -> MinF a f

deriving stock instance (Show a) => Show (MinF a f)
deriving instance Functor (MinF a)
deriving instance Foldable (MinF a)
deriving instance Traversable (MinF a)
deriving newtype instance (Eq a) => Eq (MinF a f)
deriving newtype instance (Ord a) => Ord (MinF a f)
deriving newtype instance (Num a) => Num (MinF a f)

instance (Eq a) => Eq1 (MinF a) where
  liftEq _ (MinF a) (MinF b) = a == b

instance (Ord a, Show a) => JoinSemiLattice1 e (MinF a) where
  liftLatJoin (MinF a) (MinF b) = -- trace ("min of :" <> show (a,b, min a b)) $
    Right . MinF $ min a b

data HuttonF (a :: Type) (f :: Type) where
  (:+) :: f -> f -> HuttonF a f
  HVal :: a -> HuttonF a f

deriving stock instance (Show a, Show f) => Show (HuttonF a f)
deriving instance Functor (HuttonF a)
deriving instance Foldable (HuttonF a)
deriving instance Traversable (HuttonF a)
deriving instance (Eq a, Eq f) => Eq (HuttonF a f)

instance Eq a => Eq1 (HuttonF a) where
  liftEq eq (a :+ b) (a' :+ b') =  (eq a a') && (eq b b')
  liftEq _ (HVal a) (HVal b) = a == b
  liftEq _ _ _ = False

instance (Num a, Show a, NonUnifiableErr e (HuttonF a ()))
  => JoinSemiLattice1 e (HuttonF a) where
  liftLatJoin (a :+ b) (a' :+ b') = Right $ (These a a') :+ (These b b')
  liftLatJoin (HVal a) (HVal b) = Right $ HVal (a + b)
  liftLatJoin a b = Left $ termsNotUnifiable (const () <$> a) (const () <$> b)

instance (Typeable a) => Property (Min a) where
  type From (Min a) = HuttonF a
  type To (Min a) = MinF a
  rep = Min undefined

data ConstProp (a :: Type) = ConstProp

instance (Typeable a) => Property (ConstProp a) where
  type From (ConstProp a) = HuttonF a
  type To (ConstProp a) = ConstF a
  rep = ConstProp

prt_unifyMin :: forall a e m. (Ord a
                             ,Show a
                             ,MonadProperties e m
                             ,MonadBind e m (MinF a)
                             ,forall t. MonadBind e (PropertyT m) t => MonadBind e m t
                             ,MonadAssume e m (MinF a))
           => Gen a -> PropertyT m ()
prt_unifyMin gen = do
  a <- MinF <$> forAll gen
  annotateShow a
  b <- MinF <$> forAll gen
  annotateShow b
  va <- newVar a
  annotateShow va
  vb <- newVar b
  annotateShow vb
  $lookupVar va >>= (=== Just a)
  $lookupVar vb >>= (=== Just b)
  vu <- unify va vb
  annotateShow vu
  $lookupVar va >>= (=== Just (min a b))
  $lookupVar vb >>= (=== Just (min a b))
  $lookupVar vu >>= (=== Just (min a b))
  va' <- freshenVar va
  vb' <- freshenVar vb
  vu' <- freshenVar vu
  va' === vb'
  va' === vu'

hprop_unifyMin :: H.Property
hprop_unifyMin = mkProp $ prt_unifyMin intGen

prt_unifyHutton :: forall a e m. (Ord a
                             ,Show a
                             ,MonadProperties e m
                             ,forall t. MonadBind e (PropertyT m) t => MonadBind e m t
                             ,MonadAssume e m (HuttonF a))
           => Gen a -> PropertyT m ()
prt_unifyHutton gen = do
  -- traceM "## Begin Test ##"
  a <- HVal <$> forAll gen
  b <- HVal <$> forAll gen
  va <- newVar a
  vb <- newVar b
  vc <- freeVar
  vd <- freeVar
  vap <- newVar (va :+ vc)
  vbp <- newVar (vd :+ vb)
  $lookupVar vap >>= (=== Just (va :+ vc))
  $lookupVar vbp >>= (=== Just (vd :+ vb))
  -- traceM "pre-unify"
  vu <- unify vap vbp
  -- traceM "post-unify"
  $lookupVar vu >>= \case
    Nothing -> failure
    Just (HVal _) -> failure
    Just (va' :+ vb') -> do
      va <- freshenVar va
      vb <- freshenVar vb
      va' <- freshenVar va'
      vb' <- freshenVar vb'
      va === va'
      vb === vb'
      $lookupVar va' >>= (=== Just a)
      $lookupVar vb' >>= (=== Just b)
  vap' <- freshenVar vap
  vbp' <- freshenVar vbp
  vu' <- freshenVar vu
  vap' === vbp'
  vap' === vu'
  -- traceM "## End Test ##"

hprop_unifyHutton :: H.Property
hprop_unifyHutton = mkProp $ prt_unifyHutton intGen

prt_subsumeMin :: forall a e m. (Ord a
                             ,Show a
                             ,MonadProperties e m
                             ,MonadRule e m
                             ,MonadProperties e (Rule m)
                             ,MonadBind e m (MinF a)
                             ,forall t. MonadBind e (PropertyT m) t => MonadBind e m t
                             ,MonadAssume e m (MinF a)
                             ,MonadAssume e (Rule m) (MinF a)
                             )
           => Gen a -> PropertyT m ()
prt_subsumeMin gen = do
  -- Base values
  a <- MinF <$> forAll gen
  b <- MinF <$> forAll gen
  c <- MinF <$> forAll gen
  -- Vars
  va :: Var m (MinF a) <- freeVar
  vb :: Var m (MinF a) <- freeVar
  vc :: Var m (MinF a) <- freeVar
  -- One subsumed pair
  vab :: Var m (MinF a) <- freeVar
  lift $ subsume va vab
  lift $ subsume vb vab
  -- other pair
  vbc :: Var m (MinF a) <- freeVar
  lift $ subsume vb vbc
  lift $ subsume vc vbc
  -- status
  $lookupVar va >>= (=== Nothing)
  $lookupVar vb >>= (=== Nothing)
  $lookupVar vc >>= (=== Nothing)
  $lookupVar vab >>= (=== Nothing)
  $lookupVar vbc >>= (=== Nothing)

  annotateShow va
  annotateShow vb
  annotateShow vc
  annotateShow vab
  annotateShow vbc

  doFirst :: Int <- forAll $ Gen.element [0,1,2]
  annotateShow doFirst

  case doFirst of
    0 -> do
      cover 20 "a first" True
      bindVar va a
      $lookupVar va >>= (=== Just a)
      $lookupVar vb >>= (=== Nothing)
      $lookupVar vc >>= (=== Nothing)
      $lookupVar vab >>= (=== Just a)
      $lookupVar vbc >>= (=== Nothing)
    1 -> do
      cover 20 "b first" True
      bindVar vb b
      $lookupVar va >>= (=== Nothing)
      $lookupVar vb >>= (=== Just b)
      $lookupVar vc >>= (=== Nothing)
      $lookupVar vab >>= (=== Just b)
      $lookupVar vbc >>= (=== Just b)
    2 -> do
      cover 20 "c first" True
      bindVar vc c
      $lookupVar va >>= (=== Nothing)
      $lookupVar vb >>= (=== Nothing)
      $lookupVar vc >>= (=== Just c)
      $lookupVar vab >>= (=== Nothing)
      $lookupVar vbc >>= (=== Just c)

    _ -> panic "out of range"

  $lookupVar va >>= annotateShow
  $lookupVar vb >>= annotateShow
  $lookupVar vc >>= annotateShow
  $lookupVar vab >>= annotateShow
  $lookupVar vbc >>= annotateShow

  bindVar va a
  bindVar vb b
  bindVar vc c

  $lookupVar va >>= annotateShow
  $lookupVar vb >>= annotateShow
  $lookupVar vc >>= annotateShow
  $lookupVar vab >>= annotateShow
  $lookupVar vbc >>= annotateShow

  $lookupVar va >>= (=== Just a)
  $lookupVar vb >>= (=== Just b)
  $lookupVar vc >>= (=== Just c)
  $lookupVar vab >>= (=== (Just $ min a b))
  $lookupVar vbc >>= (=== (Just $ min b c))
  --

hprop_subsumeMin :: H.Property
hprop_subsumeMin = mkProp $ prt_subsumeMin intGen

prt_subsumeMinCyclic :: forall a e m. (Ord a
                             ,Show a
                             ,Num a
                             ,MonadProperties e m
                             ,MonadRule e m
                             ,MonadProperties e (Rule m)
                             ,MonadBind e m (MinF a)
                             ,forall t. MonadBind e (PropertyT m) t => MonadBind e m t
                             ,MonadAssume e m (MinF a)
                             ,MonadAssume e (Rule m) (MinF a)
                             )
           => Gen a -> PropertyT m ()
prt_subsumeMinCyclic gen = do
  -- Base values
  a <- MinF <$> forAll gen
  b <- MinF <$> forAll gen
  c <- MinF <$> forAll gen
  -- Vars
  va :: Var m (MinF a) <- newVar a
  vb :: Var m (MinF a) <- newVar b
  vc :: Var m (MinF a) <- newVar c

  $lookupVar va >>= (=== Just a)
  $lookupVar vb >>= (=== Just b)
  $lookupVar vc >>= (=== Just c)

  lift $ subsume va vb
  lift $ subsume vb vc
  lift $ subsume vc va

  let n = min a (min b c)
      m = n - 1

  $lookupVar va >>= (=== Just n)
  $lookupVar vb >>= (=== Just n)
  $lookupVar vc >>= (=== Just n)

  bindVar va m

  $lookupVar va >>= (=== Just m)
  $lookupVar vb >>= (=== Just m)
  $lookupVar vc >>= (=== Just m)


hprop_subsumeMinCyclic :: H.Property
hprop_subsumeMinCyclic = mkProp $ prt_subsumeMinCyclic intGen

prt_subsumeUnify :: forall a e m. (Ord a
                             ,Show a
                             ,MonadProperties e m
                             ,MonadRule e m
                             ,MonadProperties e (Rule m)
                             ,MonadBind e m (MinF a)
                             ,forall t. MonadBind e (PropertyT m) t => MonadBind e m t
                             ,MonadAssume e m (MinF a)
                             ,MonadAssume e (Rule m) (MinF a)
                             )
           => Gen a -> PropertyT m ()
prt_subsumeUnify gen = do
  a <- MinF <$> forAll gen
  b <- MinF <$> forAll gen

  va :: Var m (MinF a) <- newVar a
  vb :: Var m (MinF a) <- newVar b

  $lookupVar va >>= (=== Just a)
  $lookupVar vb >>= (=== Just b)

  lift $ subsume va vb

  $lookupVar va >>= (=== Just a)
  $lookupVar vb >>= (=== Just (min a b))

  lift $ subsume vb va

  $lookupVar va >>= (=== Just (min a b))
  $lookupVar vb >>= (=== Just (min a b))

  va' <- freshenVar va
  vb' <- freshenVar vb
  va' === vb'

hprop_subsumeUnify :: H.Property
hprop_subsumeUnify = mkProp $ prt_subsumeUnify intGen
