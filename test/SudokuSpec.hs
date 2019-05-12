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
import Control.Monad.TermGraph.Class
import Control.Monad.Free

import Data.POrd
import Data.Lattice
import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

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
    | otherwise = top ( "Square cannot be both " <> show a
                        <> " and " <> show b <> "." :: String)

  latMeet (Final a) (Final b)
    | a == b = val $ Final a
    | otherwise = bot

-- | A set of values that must be unique
newtype Group a = Grp [a]

-- | A single number in the sudoku puzzle
newtype Square a = Square a

-- | This one' simple enough, if we have only one option in the list of
--   available options for a square, set the final value to that one.
finalRule :: forall m. ( MonadTermGraph m
                      , MonadLatMap Options m
                      , MonadLatMap Final m
                      , MonadProp m
                      , TermCons Square m
                      , LatCons m Final
                      , LatCons m Options
                      , LatMemb m Final  ~ Final
                      , LatMemb m Options ~ Options)
          => Term Square m -> m ()
finalRule t = do
  Square v <- getTerm t
  kOpt :: Key m Options <- getKey v
  kFin :: Key m Final  <- getKey v
  Opts s <- getLat kOpt
  case IntSet.elems s of
    h:[] -> bindLat kFin (Final h) *> pure ()
    _    -> pure ()

-- | This rule will just ensure that, when we change the final value of a square
--   the options are correctly updated. This should only come into play when
--   we manually bind a final value. Otherwise it should just be a standard
--   byproduct of what we're doing.
invFinalRule :: forall m. ( MonadTermGraph m
                      , MonadLatMap Options m
                      , MonadLatMap Final m
                      , MonadProp m
                      , TermCons Square m
                      , LatCons m Final
                      , LatCons m Options
                      , LatMemb m Final  ~ Final
                      , LatMemb m Options ~ Options)
          => Term Square m -> m ()
invFinalRule t = do
  Square v <- getTerm t
  kOpt :: Key m Options <- getKey v
  kFin :: Key m Final  <- getKey v
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
groupRule :: forall m. ( MonadTermGraph m
                      , MonadProp m
                      , Alternative m
                      , MonadLatMap Options m
                      , TermCons Group m
                      , LatCons m Options
                      , LatMemb m Options ~ Options
                      , MonadLatMap Final m
                      , LatCons m Final
                      , LatMemb m Final ~ Final)
          => Term Group m -> m ()
groupRule t = do
  Grp ss <- getTerm t
  getAlt . mconcat . map (Alt . mkUpdater) $ splits ss

  where
    mkUpdater :: (Vert m, [Vert m]) -> m ()
    mkUpdater (trig,respns) = do
      kFin :: Key m Final <- getKey trig
      Final v <- getLat kFin
      for_ respns $ \ n -> do
        kOpt :: Key m Options <- getKey n
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


-- | An edit captures a single concrete change we could make to our
--   lattice map.
--
--   When we use this within a free monad we have a
data Edit m a where

  AddTerm :: (MonadTermGraph m, TermCons t m)
    => t (Vert m) -> Edit m (Term t m)

  Put      :: (MonadLatMap v m, LatCons m v)
    => LatMemb m v -> Edit m (Key m v)

  Bind     :: (MonadLatMap v m, LatCons m v)
    => Key m v -> LatMemb m v -> Edit m (Key m v)

  Equals   :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m (Key m v)

  Subsumes :: (MonadLatMap v m, LatCons m v)
    => Key m v -> Key m v -> Edit m Bool

type KeyT t f m v = Key (TransactT t f m) v

instance Functor (TransactT t f m) where
  fmap = undefined

instance Applicative (TransactT t f m) where
  pure = undefined
  a <*> b = undefined

instance Alternative (TransactT t f m) where
  empty = undefined
  a <|> b = undefined

instance Monad (TransactT t f m) where
  a >>= b = undefined

instance (MonadLatMap v m) => MonadLatMap v (TransactT t f m) where
  data Key     (TransactT t f m) v = TKey (Key m v)
  type LatMemb (TransactT t f m) v = LatMemb m v
  type LatCons (TransactT t f m) v = LatCons m v

  putLat   :: (LatCons m v)
    => LatMemb m v
    -> TransactT t f m (KeyT t f m v)
  putLat = undefined

  getLat   :: (LatCons m v)
    => KeyT t f m v
    -> TransactT t f m (LatMemb m v)
  getLat = undefined

  bindLat  :: (LatCons m v)
    => KeyT t f m v
    -> LatMemb m v
    -> TransactT t f m (KeyT t f m v)
  bindLat = undefined

  equals   :: (LatCons m v)
    => KeyT t f m v
    -> KeyT t f m v
    -> TransactT t f m (KeyT t f m v)
  equals = undefined

  subsumes :: (LatCons m v)
    => KeyT t f m v
    -> KeyT t f m v
    -> TransactT t f m Bool
  subsumes = undefined

instance (MonadTermGraph m) => MonadTermGraph (TransactT t f m) where

  type Term t' (TransactT t f m) = Term t' m
  type Vert (TransactT t f m) = Vert m
  type TermCons t' (TransactT t f m) = TermCons t' m

  addTerm :: (TermCons t' m)
    => (t' (Vert (TransactT t f m))) -> TransactT t f m (Term t' m)
  addTerm = undefined

  getTerm :: (TermCons t' m) => Term t' m -> TransactT t f m (t' (Vert m))
  getTerm = undefined

  -- | Given a particular vertex will retrieve terms (of one type) that
  --   involve said vertex. TODO :: Consider removing this, we shouldn't need it
  -- getTerms :: (TermCons t' m) => Vert m -> TransactT t f m [t' (Vert m)]
  -- getTerms = undefined

{-
instance (MonadTermLat m) => MonadTermLat (TransactT t f m) where

  getKey :: (MonadLatMap v m, LatCons m v)
    => Vert m -> TransactT t f m (KeyT t f m v)
  getKey = undefined

  getVert :: (MonadLatMap v m, LatCons m v)
    => KeyT t f m v -> Vert m
  getVert = undefined
-}

-- We want to make the above rules apply to a new monad of ours, a transaction
-- which collects the operations that can edit a termgraph



-- TODO ::
--
--   - Define lattice instance for Options
--   - Define a rule for a group
--     -- get all consts in group, all options are grp - consts.
--
--   - W/in initial tests
--     -- create 81 verts
--     -- associate each group of verts
--     -- assign values to verts and see how those propagate as we tell
--        the system to quiesce
--     -- Test that it can catch broken assignments.
--
--   - W/in later tests
--     -- Add rule w/ only triggers when quiesced and unsolved
--        -- picks a random assignment for an ambiguous value
--        -- creates shadow network w/ that value assigned
--           -- if errors on quiesce then remove from options.
--           -- if sucessful sets all terms in parent network.
--           -- don't do anything on partial, just wait.
--
-- NOTE :: Doing this properly probably means we should have some notion
--        of task priorities and running hooks in some priority order.
