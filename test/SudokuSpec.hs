{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

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

import Intro hiding (Item)
import Hedgehog hiding (Var, Property, Group)
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
import Internal.IntBindT
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as Text

-- ## Final Value ##

newtype ConstF a f where
  ConstF :: a -> ConstF a f

deriving stock instance (Show a) => Show (ConstF a f)
deriving instance Functor (ConstF a)
deriving instance Foldable (ConstF a)
deriving instance Traversable (ConstF a)
deriving newtype instance Num a => Num (ConstF a f)

deriving newtype instance (Eq a) => Eq (ConstF a f)

instance Eq a => Eq1 (ConstF a) where
  liftEq _ (ConstF a) (ConstF b) = a == b

instance (Eq a, EqualityErr e a) => JoinSemiLattice1 e (ConstF a) where
  liftLatJoin (ConstF a) (ConstF b)
    | a == b = Right $ ConstF a
    | otherwise = Left $ valuesNotEqual a b

newtype Options a f where
  Options :: HashSet a -> Options a f

deriving stock instance (Show a) => Show (Options a f)
deriving instance Functor (Options a)
deriving instance Foldable (Options a)
deriving instance Traversable (Options a)

deriving newtype instance (Eq a) => Eq (Options a f)

instance Eq a => Eq1 (Options a) where
  liftEq _ (Options a) (Options b) = a == b

instance (Eq a, Hashable a) => JoinSemiLattice1 Text (Options a) where
  liftLatJoin (Options a) (Options b)
    | HS.null inter = Left  $ "out of options for value"
    | otherwise     = Right . Options $ inter
    where

      inter = HS.intersection a b

newtype Group a f where
  Group :: HashSet a -> Group a f

deriving stock instance (Show a) => Show (Group a f)
deriving instance Functor (Group a)
deriving instance Foldable (Group a)
deriving instance Traversable (Group a)

deriving newtype instance (Eq a) => Eq (Group a f)

instance Eq a => Eq1 (Group a) where
  liftEq _ (Group a) (Group b) = a == b

instance (Eq a, Hashable a) => JoinSemiLattice1 Text (Group a) where
  liftLatJoin (Group a) (Group b)
    | HS.null inter = Left  $ "out of options for value"
    | otherwise     = Right . Group $ inter
    where

      inter = HS.intersection a b

type CVar m = Var m (ConstF Int)
type OVar m = Var m (Options Int)
type GVar m = Var m (Group (CVar m))

type Board m = HashMap (Int, Int) (CVar m)

nums :: [Int]
nums = [1,2,3,4,5,6,7,8,9]

makeBoard :: forall m. (MonadBind Text m (ConstF Int))
  => m (Board m)
makeBoard = HM.fromList <$> traverse (\ a -> (a,) <$> freeVar) cells
  where
    cells = [(x,y) | x <- nums, y <- nums]

makeRows :: forall m. ( MonadBind Text m (ConstF Int)
                     , MonadBind Text m (Group (CVar m))
                     )
           => Board m
           -> m [GVar m]
makeRows hm = traverse getRow nums
  where
    getRow i = do
      newVar . Group . HS.fromList . catMaybes
        . map (flip HM.lookup hm) $ [(x,i) | x <- nums]

makeCols :: forall m. ( MonadBind Text m (ConstF Int)
                     , MonadBind Text m (Group (CVar m))
                     )
           => Board m
           -> m [GVar m]
makeCols hm = traverse getCol nums
  where
    getCol i = do
      newVar . Group . HS.fromList . catMaybes
        $ [HM.lookup (i,y) hm | y <- nums]

makeBoxes :: forall m. ( MonadBind Text m (ConstF Int)
                     , MonadBind Text m (Group (CVar m))
                     )
           => Board m
           -> m [GVar m]
makeBoxes hm = traverse getBox [(x,y) | x <- [1,4,7] , y <- [1,4,7]]
  where
    getBox (x,y) = do
      newVar . Group . HS.fromList . catMaybes $
        [HM.lookup (x + x',y + y') hm | x' <- [0,1,2], y' <- [0,1,2]]

setCell :: forall m. (MonadBind Text m (ConstF Int))
  => Board m -> Int -> (Int, Int) -> m ()
setCell hm v ind = case HM.lookup ind hm of
  Nothing -> panic "Invalid index"
  Just a -> do
    -- traceM $ "Setting Cell : " <> show (v,ind,a)
    _ <- bindVar a (ConstF v)
    -- traceShowM =<< $lookupVar r
    skip


data Opts = Opts

instance Property Opts where
  type From Opts = ConstF Int
  type To   Opts = Options Int
  rep = Opts

optRule :: forall m. (MonadRule Text m
                    ,MonadRule Text (Rule m)
                    ,MonadFail (Rule m)
                    ,MonadBind Text (Rule m) (Options Int)
                    ,MonadBind Text (Rule m) (ConstF Int)
                    ,MonadBind Text (Rule m) (Group (CVar m))
                    ,MonadAssume Text (Rule m) (Options Int)
                    ,MonadProperty Text Opts (Rule m)
                    ,MonadProperties Text (Rule m)
                    ,Alternative (Rule m)
                    ,Var (Rule m) ~ Var m
                    ,Eq (CVar m)
                    )
  => GVar m -> Rule m ()
optRule vg = do
  Just (Group hs) <- $lookupVar vg
  let cvars = HS.toList hs
      optPairs = [(x,y) | x <- cvars, y <- cvars, x /= y]
      updateSingles = map updateSingle cvars
      updateOpts = map (uncurry updateOpt) optPairs
  getAlt . foldMap Alt $ updateSingles <> updateOpts


  where

    numsMinus :: Int -> Options Int f
    numsMinus i = Options $ HS.difference (HS.fromList nums) (HS.singleton i)

    -- | Rule that will remove an option from the second param is the first
    --   param is fixed.
    updateOpt :: CVar m -> CVar m -> Rule m ()
    updateOpt vc vgm = do
      Just (ConstF i) <- $lookupVar vc
      vo <- Opts `propertyOf` vgm
      -- FIXME :: We can't create a new variable and perform unification since
      --         that variable (and its dirtiness) persists past after the
      --         rule runs, making it run again.
      v <- $lookupVar vo >>= \case
        Nothing -> pure $ HS.fromList nums
        Just (Options hs) -> pure hs
      _ <- bindVar vo (Options $ HS.difference v (HS.singleton i))
      skip

    -- | rule that sets the value if theres only 1 option
    updateSingle :: CVar m -> Rule m ()
    updateSingle vc = do
      vo <- Opts `propertyOf` vc
      Just (Options hs) <- $lookupVar vo
      case HS.toList hs of
        (i:[]) ->do
          bindVar vc (ConstF i) *> skip
        [] -> do
          throwError "No remaining options"
        _ -> skip

type BoardCons m =
      (MonadRule Text m
      ,MonadRule Text (Rule m)
      ,MonadFail (Rule m)
      ,MonadBind Text m (Options Int)
      ,MonadBind Text m (ConstF Int)
      ,MonadBind Text m (Group (CVar m))
      ,MonadBind Text (Rule m) (Options Int)
      ,MonadBind Text (Rule m) (ConstF Int)
      ,MonadBind Text (Rule m) (Group (CVar m))
      ,MonadAssume Text (Rule m) (Options Int)
      ,MonadProperty Text Opts (Rule m)
      ,MonadProperty Text Opts m
      ,MonadProperties Text (Rule m)
      ,Alternative (Rule m)
      ,Var (Rule m) ~ Var m
      ,Eq (CVar m)
      )

initBoard :: forall m. (BoardCons m)
          => m (Board m)
initBoard = do
  board <- makeBoard
  rows <- makeRows board
  cols <- makeCols board
  boxes <- makeBoxes board
  traverse_ (addRule . optRule @m) $ rows <> cols <> boxes
  -- traceM $ "Board : " <> show ( sort $ HM.toList board)
  pure board

type CellData = Either Int (HashSet Int)

getCell :: forall m. (BoardCons m)
  => Board m -> (Int,Int) -> m CellData
getCell b ind = case HM.lookup ind b of
  Nothing -> pure . Right . HS.fromList $ nums
  Just vc -> getCell' vc

getCell' :: forall m. (BoardCons m)
        => CVar m -> m CellData
getCell' vc = $lookupVar vc >>= \case
  Just (ConstF i) -> pure $ Left i
  Nothing -> do
    vo <- Opts `propertyOf` vc
    $lookupVar vo >>= \case
      Just (Options hs) -> pure $ Right hs
      Nothing -> pure . Right . HS.fromList $ nums

printCell :: CellData -> Text
printCell (Left i) = Text.unlines ["   "," " <> show i <> " ","   "]
printCell (Right hs) = Text.unlines [r1,r2,r3]
  where
    l i = if (HS.member i hs) then show i else "~"

    r1 = l 1 <> l 2 <> l 3
    r2 = l 4 <> l 5 <> l 6
    r3 = l 7 <> l 8 <> l 9

printBoxRow :: forall m. (BoardCons m)
   => Board m -> (Int,Int) -> m Text
printBoxRow b (x,y) = do
  ta <- ZipList . Text.lines . printCell <$> getCell b (x  ,y)
  tb <- ZipList . Text.lines . printCell <$> getCell b (x+1,y)
  tc <- ZipList . Text.lines . printCell <$> getCell b (x+2,y)
  let space = ZipList $ replicate 3 " "
  pure . Text.unlines . getZipList $ do
    a' <- ta
    b' <- tb
    c' <- tc
    s <- space
    pure $ a' <> s <> b' <> s <> c'

printBox :: forall m. (BoardCons m)
  => Board m -> (Int,Int) -> m Text
printBox b (x,y) = do
  let spaces = [Text.replicate 11 " "]
  ra <- Text.lines <$> printBoxRow b (x,y)
  rb <- Text.lines <$> printBoxRow b (x,y+1)
  rc <- Text.lines <$> printBoxRow b (x,y+2)
  pure . Text.unlines $ ra <> spaces <> rb <> spaces <> rc

printBoardRow :: forall m. (BoardCons m)
  => Board m -> Int -> m Text
printBoardRow b y = do
  ba <- ZipList . Text.lines <$> printBox b (1,y)
  bb <- ZipList . Text.lines <$> printBox b (4,y)
  bc <- ZipList . Text.lines <$> printBox b (7,y)
  let sep = ZipList $ replicate 11 " | "
  pure . Text.unlines . getZipList $ do
    a' <- ba
    b' <- bb
    c' <- bc
    s <- sep
    pure $ a' <> s <> b' <> s <> c'

printBoard :: forall m. (BoardCons m)
  => Board m -> m Text
printBoard b = do
  ra <- Text.lines <$> printBoardRow b 1
  rb <- Text.lines <$> printBoardRow b 4
  rc <- Text.lines <$> printBoardRow b 7
  let hsep = Text.replicate 11 "-"
      hsep' = [hsep <> "-+-" <> hsep <> "-+-" <> hsep]
  pure . Text.unlines $ ra <> hsep' <> rb <> hsep' <> rc


prt_basicSudoku :: forall m. (BoardCons m)
             => PropertyT m ()
prt_basicSudoku = do
  x <- forAll $ Gen.element nums
  y <- forAll $ Gen.element nums
  -- n <- forAll $ Gen.element nums
  b <- lift initBoard
  annotate =<< (lift $ convertString <$> printBoard b)
  boards <- lift $ traverse (\ x -> do
                       setCell b x (10-x,y)
                       (<> "\n ## \n\n") <$> printBoard b
                   ) [r | r <- nums, r /= x]
  traverse (annotate . convertString) boards
  annotate =<< (lift $ convertString <$> printBoard b)

hprop_basicSudoku :: H.Property
hprop_basicSudoku = mkProp $ prt_basicSudoku

prt_failSudoku :: forall m. (BoardCons m)
             => PropertyT m ()
prt_failSudoku = do
  b <- lift initBoard
  _ <- forM ([0..] :: [Int]) $ \ _ -> do
    x <- forAll $ Gen.element nums
    y <- forAll $ Gen.element nums
    n <- forAll $ Gen.element nums
    lift $ setCell b n (x,y)
    --traceM $ "setting : " <> show ((x,y),n)
    --traceM =<< (lift $ printBoard b)
    annotate =<< (lift $ convertString <$> printBoard b)
  skip

hprop_failSudoku :: H.Property
hprop_failSudoku = mkFailProp $ prt_failSudoku
