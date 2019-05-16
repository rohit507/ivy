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

import Ivy.Prelude
import Control.Monad.Lat.Class


-- Want to detect undermatch vs overmatch
-- I.e. if e expect to see a (a :+ b) and get a vert, then it's an undermatch
--      if I expect to see a (a :+ b) and get a (a :- b) it's an overmatch and
--      can be treated as a permanent failure.
