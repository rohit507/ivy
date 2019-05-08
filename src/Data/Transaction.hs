{-|
Module      : Data.Transaction
Description : Type of suspended computations over a set of triggers.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

FIXME :: Concept needs better name -_-
-}

module Data.Transaction where

import Ivy.Prelude
import Data.Functor (fmap)

-- | A transaction is a way to build an action (in f) bit by bit, when
--   various triggers are hit. In particular we watch for various events to
--   happen, and as they do, build up some operation that can later be run.
--
--   Importantly, you can compose transactions in parallel (if m has an
--   alternative instance) and in serial (if f has an applicative instance)
data Transaction t f m a where

  Watch :: HashMap t (t -> m (Transaction t f m a)) -> Transaction t f m a

  Run :: f () -> Transaction t f m ()

  Pure :: a -> Transaction t f m a

instance (Eq t, Hashable t, Alternative m, Applicative f)
  => Semigroup (Transaction t f m a) where

  -- NOTE :: We use the Semigroup instance of `Alt` (in Data.Monoid) to allow the
  -- semigroup instance of HashMap to work over the transactions we return.
  -- With the appropriate choice of alternative instance (`Compose [] Lat`?)
  -- we should be able to extract a list of all the new transactions that were
  -- created.
  --
  -- The big problem here is with duplication of rules. If a rule creates
  -- another rule, should we delete the first?
  --
  -- In the case where create different rules based on what a particular
  -- variable resolves to. Well, it should be an upwards closed function that
  -- differentiates between cases so if one choice is taken the other shouldn't
  -- be.
  --
  -- I guess the case that's weird is if the created rules aren't a flat lattice,
  -- instead becoming something else yet. We might need to keep track of child
  -- rules as we run (each parent rule should have at most one child per object?)
  --
  (Watch m) <> (Watch m') = Watch . unAlt $ wrapAlt m <> wrapAlt m'
    where
      wrapAlt :: HashMap k (k -> m r) -> HashMap k (k -> Alt m r)
      wrapAlt = map (map Alt)

      unAlt :: HashMap k (k -> Alt m r) -> HashMap k (k -> m r)
      unAlt = map (map getAlt)

  -- When we have just have two free monads of edits we can concat them to get
  -- the resulting output.
  (Run f) <> (Run f') = Run $ f *> f'

  -- If we have a run and a watch, we watch on the relevant variables and
  -- append the potential side-effects together. Done this way, if we
  -- can create a sandbox for the edit operation, we can run an operation
  -- inside the sandbox and only commit them if certain conditions are met.
  -- (Hmm, flattened sandboxes == provenance == predicated operations. Just
  --  add an interpretation function that will turn a forall into a rule.)
  -- Making decisions with provenance seems like a bad idea.
  Run e   <> Watch m = Watch . map (\ fk k -> (Run e <>) <$> fk k) $ m
  Watch m <> Run e   = Watch . map (\ fk k -> (<> Run e) <$> fk k) $ m


instance (Eq t, Hashable t, Alternative m, Applicative f)
  => Monoid (Transaction t f m a) where

  mempty = Run $ pure ()

newtype TransactT t f m a
  = TransactT { getTransact :: m (Transaction t f m, a) }

instance Functor m => Functor (TransactT t f m) where
  fmap f (TransactT m) = TransactT $ (\ (a,b) -> (a, f b)) <$> m

instance (Eq t, Hashable t, Applicative f, Alternative m, Monad m)
  => Applicative (TransactT t f m) where

  pure a = TransactT $ pure (mempty, a)

  TransactT mf <*> TransactT ma = TransactT $ do
    (t , f) <- mf
    (t', a) <- ma
    pure (t <> t', f a)

instance (Eq t, Hashable t, Applicative f, Alternative m, Monad m)
  => Monad (TransactT t f m) where

  TransactT ma >>= f = TransactT $ do
    (t, a) <- ma
    (t', b) <- getTransact . f $ a
    pure (t <> t', b)
