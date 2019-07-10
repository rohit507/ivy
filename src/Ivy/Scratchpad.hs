{---# LANGUAGE AllowAmbiguousTypes #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.Scratchpad where

import Ivy.MonadClasses
import Ivy.Prelude
import Control.Lens
import Control.Lens.TH
import Ivy.Wrappers.IntMap (IntMap)
import qualified Ivy.Wrappers.IntMap as IM
import Ivy.Wrappers.IntSet (IntSet)
import qualified Ivy.Wrappers.IntSet as IS
import Ivy.Wrappers.IntGraph (IntGraph)
import qualified Ivy.Wrappers.IntGraph as IG
-- import qualified Data.IntMap as M
-- import Data.TypeMap.Dynamic (TypeMap)
-- import qualified Data.TypeMap.Dynamic as TM

data Config = Conf {}


data State m = State {
     termData :: IntMap ETermID (TermState m)
   }

newtype ETermID = ETID { getETID :: Int }

instance Newtype ETermID Int where
  pack = ETID
  unpack = getETID

newtype TermID t = TID { getTID :: Int}

instance Newtype (TermID t) Int where
  pack = TID
  unpack = getTID


-- | The unique state information we store for each term.
data TermState m where
  TermState :: {
       termType :: TypeRep t
     , termValue :: Maybe (t (Var t m))
     , dirty :: Bool
     } -> TermState m
  Unified :: TypeRep t -> TermID t -> TermState m
  Errored :: (MonadError e m) => e -> TermState m

-- | Pure and Slow Transformer that allows for most of the neccesary binding
--   operations.
type IntBindT m = RWST Config () (State m) m


-- TODO ::
--    - Property tests
--    - core implementation of unification
--

      -- Consider converting to a typed map, at least early on.
      -- TODO :: Should we keep a graph of term relationships or something?
      --         That would hopefully let us minimize the number of terms we
      --         update, and let us keep better track of subsumption, esp
      --         when a cycle occurs and a sequence of terms should be unified.
      --
      --   - Okay so we get three graphs
      --       - Basic dependency graph w/in a term type
      --       - subsumption graph where cycle detection can lead to the
      --         collapsing of term
      --       - edge-labeled relationship graph which we can use to
      --         project or inject rules when needed.
      --
      --   - What happens if we're strict w.r.t to hooks?
      --       - well, we open ourselves up to infinite cycles or indefinite
      --         expansion of the graph as rules trigger and re-trigger.
      --   - What happens if we're lazy?
      --       - we have to do more work to keep proper track of whether
      --         we have cycles in chains of actions, and them resolve them
      --         somehow.
      --         - So let's walk through that : We have a <- b <- c <- a
      --           we start when b changes and we run the relevant rules
      --           if c is also dirty, then we run through those terms.
      --           if a is dirty then we can run through its rules
      --           well, then we hit b again.
      --           - At which point we notice that b is practically dirty
      --             and move through the relevant steps again.
      --           - Of course, we could be co-inductive and assume that
      --             b is clean and just run one iteration of the cycle.
      --             - when we recurse back to that first call then we could
      --               notice that b was in the set of operations we actually
      --               leaned on our co-inductive assumption.
      --             - And then what? if we notice that we have changed b
      --               we rerun the process?
      --             - well, we could put a counter down and limit the
      --               number of cycles to some parameter?
      --   - Of course laziness needs an additional assumption for it to
      --     be correct which is that no rule will take a bottom and
      --     turn it into something higher than bottom on the lattice.
      -- Sigh :| i need to think about testing all this stuff, especially
      -- ensuring that the partial order / lattice properties are well met.
      -- Likewise, Testing the correctness of hooks would be super nice.
      --
      -- Hooks are going to be the hard part here, since we need to
      -- basically do some silly continuation based stuff that
      -- allows us to split and merge hooks.
      --
      -- So we need a bunch of specific properties for a hook:
      --   it has a nominal breadth and height, where breadth is the number of
      --   parallel actions composed into a single chain.
      --   The height is number of remaining steps in the longest of those
      --   actions.
      --
      -- We need to make sure that, unless an external bind is applied, then
      -- we always reduce the number of steps remaining.
      --
      -- Thankfully, the hook layer should be pretty independent of the
      -- attempt structure, especially when we can just keep an old state
      -- hiding somewhere and swap it in when we mess up. Having that model
      -- hopefully means we don't have to super picky (for now) about keeping
      -- hooks revertible.
      --
      -- So Okay, what can these hooks do?
      --    Unify / Subsume / Bind etc...
      --    Watch for changes in a term, filter on some upwards
      --       closed property
      --    Spawn multiple parallel hooks
      --    Ideally we would be able:
      --        detect that trees are identical and keep from duplicating them
      --        prune action trees that are unachiveable.
      --    hold until a term is subsumed by another, hold until terms are
      --    equal.
      --
      --    I guess there will also probably be some way to update a hook as
      --    bindings change.
      --
      -- Boy oh boy :V and then once that's done we can focus on wrapping things
      -- up neatly. And preventing a lot of single level decomp
