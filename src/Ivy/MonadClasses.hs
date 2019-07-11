
{-# LANGUAGE AllowAmbiguousTypes #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.MonadClasses where

import Ivy.Prelude

-- * These classes are components of a somewhat modified version of
--   `Control.Unification.BindingMonad` from `unification-fd`. It
--   still performs structural unification, but with a few key differences:
--
--     1) It doesn't choke on cyclic terms.
--     2) Provides a rollback mechanism that can still return information
--        from reverted branches of execution.
--     3) Triggers hooks when terms are unified.
--
--   All of these properties are desired if we want to use unification
--   as a significant part of a synthesis process, or as an element in the
--   analysis of inherently cyclic term graphs.
--
--   TODO :: Should we go back to being more explicit about the type of each
--           term in our graph, rather than definingn to be made is about whether we
--          split up the union-find and definitional layers or have them
--          both handled by a single monolith.
--
--          - The former should be more reusable, since we're squishing the
--            term level semantics of a bunch of things down flat.
--
--          - The latter would likely be faster and easier to optimize.
--            I suspect it would be faster to build, but not as simple
--            to manipulate.


-- | This monad gives you the ability to unify terms in some unifiable language.
class MonadBind t m => MonadUnify t m  where

  -- | This allows you to unify terms in your given context.
  unify :: (Unifiable e t, MonadError e m) => Var t m -> Var t m -> m (Var t m)

  -- | Tells us whether two terms have been unified. Does not change
  --   the state of the update, just return information.
  equals :: (Unifiable e t, MonadError e m) => Var t m -> Var t m -> m Bool

  -- TODO :: I'm not confident that we want an equiv operation since
  --        that may break the upwards closed nature of our various operations
  --        It's kinda unclear.
  --
  --   Hell it isn't even clear that the core binding operations need
  --   to be upwards closed in some fashion.
  --
  --   Tells us whether the input terms are equivalent modulo renaming of
  --   free variables. If they are, returns a set of unifications that
  --   need to occur for both terms to be truly equivalent.
  --   equiv :: Var m t -> Var m t -> m (Maybe [(Var m t, Var m t)])

-- | A property is a many-to-one relationship between two terms of potentially
--   different types.
class (Eq p, Ord p, Hashable p) => Property p t t' | p -> t, p -> t'

-- | A binding monad that can support property relations between terms.
--
--   NOTE: A very important note is that when you unify two terms with the same
--         property then the terms those properties point to will also be
--         unified!
class MonadProperty p m where

  -- | Retrieve the term re
  propertyOf :: (Property p t t', MonadBind t m, MonadBind t' m)
             => p -> Var m t -> m (Var m t')

{-
-- | Lets you define how unification works for some specific type of term.
--
--   Ideally this would either be some JoinSemiLattice or the fixed point of a
--   higher-order join semilattice.
--   Those instances will be coming I suppose.
class Unifiable e t where

   -- | TODO :: see if we can better integrate with the partial order model
   --           that we're using elsewhere.
   --
   --           in particular unifiable e t should be structurally equivalent to
   --           JoinSem iLattice1 e t.
   unifyTerm :: (MonadError e m, MonadUnify t m) => t v -> t v -> m (t v)
-}

-- | Monads that allow you to bind variables to terms.
class MonadBind t m where

  -- | This is a variable that has a unifiable term associated with it.
  type Var t m = r | r -> t m

  -- | Create a new free (unbound) variable. The proxy term is a bit annoying
  --   but at least it helps ensure that everything is properly typed without
  --   requiring a whole pile of extra effort.
  freeVar :: (MonadError e m, Unifiable e t) => proxy t -> m (Var t m)

  -- | Get the single layer term for some variable or `Nothing` if
  --   the var is unbound.
  lookupVar  :: (MonadError e m, Unifiable e t) => Var t m -> m (Maybe (t (Var t m)))

  -- | Binds a variable to some term, overwriting any existing term for that
  --   variable if needed.
  bindVar :: (MonadError e m, Unifiable e t) => Var t m -> t (Var t m) -> m (Var t m)

class (MonadBind t m, MonadUnify t m) => MonadSubsume t m where

  -- | Asserts that the first var subsumes the second.
  subsume :: Var t m -> Var t m -> m ()

  -- | Asks whether the first variable is <= the second
  subsumes :: Var t m -> Var t m -> m Bool





-- | A class for monads that can attempt a computation and if that computation
--  fails rewind state and run some recovery operation
class (Monad m) => MonadAttempt m where

  -- | Try an update, if the action should be rolled back (returns a `Left f`)
  --   then do so, and run the recovery function.
  --
  --   Keep in mind that the f here isn't actually an error per-se, just
  --   some knowledge that has been gained from the rolled back computation.
  --   E.g. if you're doing CDCL `f` could be a newly learned conflict clause.
  --
  --   NOTE: We're not using something like LogicT because this interface works
  --         better with the push-pop interface of incremental SMT solving.
  attempt :: m (Either f b) -> (f -> m b) -> m b


-- | The default implementation of Attempt for a monad transformer on top of
--   a MonadAttempt.
--
--   You need to provide the instructions on how to compose and decompose
--   the state for that monad transformer.
--
--   If an error is thrown during the attempted action then we revert the
--   action, but allow the error to continue propagating. This seems like
--   the least bad way to handle the problem. The bindings that triggered
--   the error may well be missing due to rolling things back, but at least
--   you're in a coherent state of some sort that you might be able to
--   recover from.
--
--   NOTE :: If you disagree with the above, I'd be happy to listen to why.
defaultLiftAttempt :: forall t m f b e. (MonadTransControl t,
                                      MonadAttempt m,
                                      Monad (t m),
                                      MonadError e (t m)
                                     )
                   => (forall a. StT t a -> (StT t (), a))
                   -> (forall a. (StT t (), a) -> StT t a)
                   -> t m (Either f b)
                   -> (f -> t m b)
                   -> t m b
defaultLiftAttempt extractState insertState act recover = do
  initState <- captureT
  result <- liftWith $ \ run ->
    attempt (act' run) $ recover' run initState
  restoreT $ pure result
    where

      -- | We wrap our action in a catchError block so that we can well,
      --   catch the errors.
      wAct :: t m (Either (Either e f) b)
      wAct = catchError (first Right <$> act) (pure . Left . Left)


      act' :: Run t -> m (Either (Either e f) (StT t b))
      act' run = extractState <$> (run @_  @(Either (Either e f) b) wAct) >>= pure . \case
        (st, Right b) -> Right $ insertState (st, b :: b)
        (_ , Left  f) -> Left  f

      recover' :: Run t -> StT t () -> Either e f -> m (StT t b)
      recover' run initSt f
        = run $ restoreT (pure initSt) >>= (\ () -> case f of
            (Left e) -> throwError e
            (Right f') -> recover f')


-- So what we want:
--
--    Term Graph w/ vertices in a language and relations to terms in multiple
--    related languages.
--
--    newVar :: m (Vert t m)
--
--    The ability to attempt a computation and then rewind state if/when there's
--    an issue.
--
--    Define unification rules for each type of term in the language
--    Define hooks that trigger when the definition of a term is updated
