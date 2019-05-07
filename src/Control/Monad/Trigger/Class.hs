{-|
Module      : Control.Monad.Trigger.Class
Description : Class for monads
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Control.Monad.Trigger.Class where

import Ivy.Prelude

-- | This is a monad for triggering actions when triggers `t` are triggered.
--   It doesn't specify enting about the run model (seq, parrelel,
--   single-threaded, multi-threaded, prioritized, etc...)
class (Monad m) => MonadTrigger t m where

  -- | This will take an action that is triggered when a particular key
  --   has changed, and add it to a queue.
  pushHook :: t -> (t -> m ()) -> m ()

  -- | This will pop some pending hook from the queue of available hooks.
  --   This should remove the hook from the queue and return Nothing if there
  --   are no remaining hooks to trigger.
  popHook :: m (Maybe (t, m ()))

  -- | This will trigger a set of hooks, moving them into the (abstract) run
  --   queue to be executed as needed.
  trigger :: t -> m ()
