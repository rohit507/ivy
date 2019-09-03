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

module Internal.IntBindT where

import Intro hiding (Item)
import Hedgehog hiding (Var, Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog.Internal.Distributive
import Control.Concurrent.Supply
import Control.Monad.Morph
import Ivy.Prelude
import Algebra.Lattice
import Ivy.MonadClasses
import Ivy.IntBindT
import Ivy.ErrorClasses
import Ivy.Testing ()

type BindM e = IntBindT (ExceptT e IO)

defaultConf :: Config
defaultConf = Config

mkProp :: PropertyT (BindM Text) () -> H.Property
mkProp prop = property $ withBindM defaultConf prop >>= \case
  Left e -> panic $ "Threw Error : " <> show e
  Right () -> skip

mkFailProp :: PropertyT (BindM Text) () -> H.Property
mkFailProp prop = property $ withBindM defaultConf prop >>= \case
  Left _ -> skip
  Right () -> panic $ "Expected error, got result instead"

withBindM :: forall a e. (Show e) => Config -> PropertyT (BindM e) a -> PropertyT IO (Either e a)
withBindM conf = runExceptT . distributeT . hoist morph

  where

    morph :: BindM e b -> ExceptT e IO b
    morph m = do
      supply <- liftIO newSupply
      (a, _, _) <- runIntBindT conf supply m
      pure a

intGen :: Gen Int
intGen = Gen.int (Range.linear 0 20)
