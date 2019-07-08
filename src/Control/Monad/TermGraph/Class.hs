{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : Control.Monad.TermGraph.Class
Description : Class for monads which can store a graph where edges are
              terms in grammar.
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Control.Monad.TermGraph.Class where

import Ivy.Prelude

-- * So what we need here is a class that captures the full stack of operations
--   currently in Sketchpad.hs
