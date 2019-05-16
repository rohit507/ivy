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

module SudokuSpec where

import Ivy.Prelude
import Control.Monad.Lat.Class
import Control.Monad.LatMap.Class
import Control.Monad.Prop.Class
import Control.Monad.PropRule.Class
import Control.Monad.TermGraph.Class
import Control.Monad.Free

import Data.POrd
import Data.Lattice
import Data.Transaction
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.HashMap.Lazy as HashMap

import GHC.Base (fmap)

-- | Set of potential options for each value in the grid.
newtype Options = Opts IntSet
  deriving (Show, Eq)

instance POrd Options where
  lessThanOrEq    (Opts a) (Opts b) = b `IntSet.isSubsetOf` a
  lessThan        (Opts a) (Opts b) = b `IntSet.isProperSubsetOf` a
  greaterThanOrEq (Opts a) (Opts b) = a `IntSet.isSubsetOf` b
  greaterThan     (Opts a) (Opts b) = a `IntSet.isProperSubsetOf` b

instance Lattice Options where

  type LatErr m Options = (IsLatErr m String)

  latJoin (Opts a) (Opts b)
    | IntSet.null c = top
      ("There are no valid options for this square." :: String)
    | otherwise = val $ Opts c
    where
      c = IntSet.intersection a b

  latMeet (Opts a) (Opts b)
    | IntSet.fromList [1..9] `IntSet.isSubsetOf` c = bot
    | otherwise = val $ Opts c
    where
      c = IntSet.union a b

newtype Final = Final Int
  deriving (Show, Eq)

instance POrd Final where
  lessThanOrEq = (==)
  lessThan _ _ = False
  greaterThanOrEq = (==)
  greaterThan _ _ = False

instance Lattice Final where

  type LatErr m Final = (IsLatErr m String)

  latJoin (Final a) (Final b)
    | a == b = val $ Final a
    | otherwise = top ( "Cell cannot be both " <> show a
                        <> " and " <> show b <> "." :: String)

  latMeet (Final a) (Final b)
    | a == b = val $ Final a
    | otherwise = bot

-- | A set of values that must be unique
newtype Group a = Grp [a]

-- | A single number in the sudoku puzzle
newtype Cell a = Cell a

-- | This one' simple enough, if we have only one option in the list of
--   available options for a square, set the final value to that one.
finalRule :: forall m e. ( MonadTermGraph m
                      , MonadLatMap Options m
                      , MonadLatMap Final m
                      , MonadPropRule Options m
                      , MonadPropRule Final m
                      , MonadError e m
                      , TransactionErr e
                      , Typeable m
                      , TermCons Cell m
                      , LatCons m Final
                      , LatCons m Options
                      , LatMemb m Final  ~ Final
                      , LatMemb m Options ~ Options)
          => Term Cell m -> Transaction m ()
finalRule t = do
  Cell v <- getTerm t
  kOpt :: KeyT m Options <- getKey v
  kFin :: KeyT m Final   <- getKey v
  Opts s <- getLat kOpt
  case IntSet.elems s of
    [h] -> bindLat kFin (Final h) *> pure ()
    _    -> pure ()

-- | This rule will just ensure that, when we change the final value of a square
--   the options are correctly updated. This should only come into play when
--   we manually bind a final value. Otherwise it should just be a standard
--   byproduct of what we're doing.
invFinalRule :: forall m e. ( MonadTermGraph m
                      , MonadLatMap Options m
                      , MonadLatMap Final m
                      , MonadPropRule Final m
                      , MonadPropRule Options m
                      , TermCons Cell m
                      , MonadError e m
                      , Typeable m
                      , TransactionErr e
                      , LatCons m Final
                      , LatCons m Options
                      , LatMemb m Final  ~ Final
                      , LatMemb m Options ~ Options)
          => Term Cell m -> Transaction m ()
invFinalRule t = do
  Cell v <- getTerm t
  kOpt :: KeyT m Options <- getKey v
  kFin :: KeyT m Final  <- getKey v
  Final s <- getLat kFin
  bindLat kOpt (Opts . IntSet.singleton $ s)
  pure ()

-- | Generate a list of single elements and remainders from an input list.
splits :: [a] -> [(a,[a])]
splits [] = []
splits (a:as) = (a,as) : map (\ (x,xs) -> (x,a:xs)) (splits as)

-- | Here, we create a bunch of rules in parallel. One for each
--   element in the group.
--
--   If that element gets set to an actual value, then we remove those
--   options from all the other elements in the group.
--
--   It's important that we use `Alt` (i.e. Monoid for `<|>`) to compose them
--   so that each term in the group can trigger a chain of updates.
--   If we don't, then the system will require every element of the group
--   to have a final value before propagating anything.
groupRule :: forall m e. ( MonadTermGraph m
                      , MonadPropRule Options m
                      , MonadPropRule Final m
                      , Alternative m
                      , Typeable m
                      , MonadError e m
                      , TransactionErr e
                      , MonadLatMap Options m
                      , MonadLatMap Final m
                      , TermCons Group m
                      , LatCons m Options
                      , LatMemb m Options ~ Options
                      , MonadLatMap Final m
                      , LatCons m Final
                      , LatMemb m Final ~ Final)
          => Term Group m -> Transaction m ()
groupRule t = do
  Grp ss <- getTerm t
  getAlt . mconcat . map (Alt . mkUpdater) $ splits ss

  where
    mkUpdater :: (Vert m, [Vert m]) -> Transaction m ()
    mkUpdater (trig,respns) = do
      kFin :: KeyT m Final <- getKey trig
      Final v <- getLat kFin
      for_ respns $ \ n -> do
        kOpt :: KeyT m Options <- getKey n
        bindLat kOpt (holeOpt v)

-- | This rigamarole lets us cache the options that are missing one
--   element instead of rebuilding them repeatedly. Admittedly, this
--   shouldn't be entirely neccesary for such a small problem.
makeHole :: Int -> Options
makeHole h = Opts . IntSet.fromList $ [n | n <- [1..9] , n /= h]

holeMap :: IntMap Options
holeMap = IntMap.fromList $ zip [1..9] (map makeHole [1..9])

holeOpt :: Int -> Options
holeOpt h = holeMap IntMap.! h

makeSudoku :: forall m e. ()
           => m (IntMap (Vert m))
makeSudoku = undefined
  where

    makeCell :: m (IntMap (Vert m))
    makeCell = undefined -- TODO :: Don't forget to add the Cell terms.

    makeRow :: IntMap (Vert m) -> Int -> m ()
    makeRow = undefined

    makeCol :: IntMap (Vert m) -> Int -> m ()
    makeCol = undefined

    makeSquare :: IntMap (Vert m) -> (Int, Int) -> m ()
    makeSquare = undefined

printSudoku :: IntMap (Vert m) -> m String
printSudoku = undefined

setCell :: IntMap (Vert m) -> Int -> Int -> m ()
setCell = undefined

-- Make the 81 verts
-- make each row
-- make each col
-- make each square
