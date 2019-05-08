{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : Control.Monad.Lang.Types
Description : Datatypes and instances we use when implementing a LangT
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Data.Functor.Foldable.Reify (
    reifyRecursive
  , reifyTraverse
  , reifyRecursives
  , TGraph(..)
  , showTGraph
  ) where

import EDGPrelude
import Data.Reify
import Data.Reify.Graph
import Data.Functor.Foldable
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict as HashMap
import Data.List (sortOn)

-- import Data.Functor.Compose

newtype MuReify a = MuR { getRec :: a }

type instance Base (MuReify a) = Base a

instance (Recursive t, Traversable (Base t)) => MuRef (MuReify t) where
  type DeRef (MuReify t) = Base t

  mapDeRef f = traverse (f . MuR) . project . getRec

-- | Allows you to automatically reify a recursive datatype into its base
--   graph. the recursion-schemes library gives you tools to generate
--   the Functors for recursive datatypes, so why not use them?
reifyRecursive :: (Recursive s, Traversable (Base s)) => s -> IO (Graph (Base s))
reifyRecursive = reifyGraph . MuR

newtype ComposeMuRef g h = CMR (g h)
newtype ComposeDeRef g h f = CDR (Either (g f) (h f))
newtype ComposeWrap (g :: * -> *) h = CW h

data TGraph g h = TGraph { netlist :: [(Unique, h Unique)]
                     , start :: g Unique}

showTGraph :: (Show (g Int), Show (h Int)) => TGraph g h -> String
showTGraph (TGraph netlist start) = unlines $ lets ++ [ins]
  where
    lets = zipWith (++)
      ("let ": repeat "    ")
      [show u ++ " = " ++ show e | (u,e) <- sortOn fst netlist]
    ins = "  in " ++ show start

instance (Functor g, Functor h) => Functor (ComposeDeRef g h) where
  fmap f (CDR (Left g)) = CDR . Left $ fmap f g
  fmap f (CDR (Right h)) = CDR . Right $ fmap f h

instance (Foldable g, Foldable h) => Foldable (ComposeDeRef g h) where
  foldMap f (CDR (Left g)) = foldMap f g
  foldMap f (CDR (Right h)) = foldMap f h


instance (Traversable g, Traversable h) => Traversable (ComposeDeRef g h) where
  traverse f (CDR (Left g)) = CDR . Left <$> traverse f g
  traverse f (CDR (Right h)) = CDR . Right <$> traverse f h

type instance Base (ComposeMuRef g h) = ComposeDeRef g (Base h)

instance (Traversable (DeRef h), MuRef h) => MuRef (ComposeWrap g h) where

  type DeRef (ComposeWrap g h) = ComposeDeRef g (DeRef h)

  mapDeRef f (CW h) = CDR . Right <$> mapDeRef (f . CW) h

instance (Traversable g
         , Traversable (DeRef h)
         , MuRef h)
        => MuRef (ComposeMuRef g h) where

  type DeRef (ComposeMuRef g h) = ComposeDeRef g (DeRef h)

  mapDeRef f (CMR g) = CDR . Left <$> traverse (f . CW) g

-- | If you have a traversable of reifiable elements, this will reify them
--   all as a group attempting to preserve observable sharing as much as
--   possible over the entire group.
reifyTraverse :: ( Traversable g
                , Traversable (DeRef h)
                , MuRef h)
              => g h -> IO (TGraph g (DeRef h))
reifyTraverse g = separateGraph <$> reifyGraph (CMR g)

  where

    missingG = error "Did not find outer traversable g in list of terms."
    gIsRight = error "Outermost element is not the traversable g"
    hIsLeft  = error "Inner element is not a member of type `DeRef h Unique`."

    getG t gu = case EDGPrelude.lookup gu t of
      Nothing -> missingG
      Just (CDR (Right _)) -> gIsRight
      Just (CDR (Left v)) -> v

    removeLeft _ (a, CDR (Right s)) = [(a,s)]
    removeLeft g (a, CDR (Left  _))
      | a == g = []
      | otherwise = hIsLeft

    separateGraph (Graph t g) = TGraph (t >>= removeLeft g) (getG t g)

reifyRecursives :: (Traversable g, Traversable (Base h), Recursive h)
                => g h -> IO (TGraph g (Base h))
reifyRecursives = reifyTraverse . fmap MuR
