{-# LANGUAGE UndecidableInstances #-}

{-|
Module      : Ivy.Prelude
Description : The prelude we use throughout this library
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX
-}

module Ivy.Prelude (
    module P
  , modifyError
  , listens
  , censor
  , maybeM
  , liftEither
  , whenJust
  , matchType
  , matchType2
  , mappendMaybe
  , mappendMaybes
  , force
  , errEq
  , GetErr(..)
  , crushThese
) where

import Intro hiding (Item)
import qualified Text.Show as S
import Data.TypeMap.Dynamic (TypeMap, Item, OfType)
import qualified Data.TypeMap.Dynamic as TM
import Type.Reflection as P
import Data.Dynamic as P
import Data.Constraint as P hiding (top)
import Data.Bifoldable as P
import Data.Bitraversable as P
import Data.Functor.Foldable as P hiding (fold, embed, hoist)
import Data.Functor.Foldable.TH as P
import Data.Functor.Classes as P (liftEq, showsPrec1)
import Control.Monad.Trans.Control as P hiding (embed)
import Data.Reify as P
import Hedgehog as P (showsPrec1)
-- import Control.Monad.Free.Church as P
import Control.Monad.Morph as P
import Control.Newtype as P
import GHC.TypeLits as P
import Control.Concurrent.Supply as P
import Control.Lens as P hiding (para, under, over, op, ala, Context)
import Data.These as P
import Control.Monad.Operational as P hiding (view)
import Control.Monad.Logic as P hiding (fail)
import Data.Constraint.Unsafe
import qualified Control.Monad.Fail as B (fail,MonadFail)

crushThese :: These (Maybe a) (Maybe b) -> Maybe (These a b)
crushThese = \case
  This Nothing   -> Nothing
  This (Just ta) -> Just $ This ta
  --
  That Nothing   -> Nothing
  That (Just tb) -> Just $ That tb
  --
  These Nothing   Nothing   -> Nothing
  These (Just ta) Nothing   -> Just $ This ta
  These Nothing   (Just tb) -> Just $ That tb
  These (Just ta) (Just tb) -> Just $ These ta tb

instance (Show a) => Show (TypeMap (OfType a)) where
  show tm = "(empty" <> mconcat (TM.toList @String (TM.map printMember tm)) <> ")"
    where
      printMember :: forall t. Typeable t => Proxy t -> a -> String
      printMember p a = " <: (" <> show p <> ", " <> show a <> ")"

errEq :: forall e m. (MonadError e m) :- (e ~ Err m)
errEq = unsafeCoerceConstraint

class GetErr (m :: Type -> Type) where
  type Err m :: Type

instance GetErr (ExceptT e m) where
  type Err (ExceptT e m) = e


instance GetErr (Either e) where
  type Err (Either e) = e

instance (GetErr m) => GetErr (StateT s m) where
  type Err (StateT s m) = Err m

instance (GetErr m) => GetErr (ReaderT r m) where
  type Err (ReaderT r m) = Err m

instance (GetErr m) => GetErr (WriterT w m) where
  type Err (WriterT w m) = Err m

instance (GetErr m) => GetErr (RWST r w s m) where
  type Err (RWST r w s m) = Err m

instance (GetErr m) => GetErr (LogicT m) where
  type Err (LogicT m) = Err m

instance (GetErr m) => GetErr (ProgramT n m) where
  type Err (ProgramT n m) = Err m

instance MonadError e m => MonadError e (ProgramT n m) where
  throwError = lift . throwError
  catchError a h = join . lift $ (viewT a) >>= \case
    Return a -> pure . pure $ a
    instr :>>= f -> pure $ singleton instr >>= (\ b -> catchError (f b) h)

instance (Monad m, Alternative m) => Alternative (ProgramT n m) where
  empty = lift empty
  a <|> b = join . lift $ (viewT a <|> viewT b) >>= \case
    Return a -> pure . pure $ a
    inst :>>= f -> pure $ singleton inst >>= f

instance (MonadPlus m) => MonadPlus (ProgramT n m) where
  mzero = lift mzero
  mplus a b = join . lift $ (mplus (viewT a) (viewT b)) >>= \case
    Return a -> pure . pure $ a
    inst :>>= f -> pure $ singleton inst >>= f

instance (B.MonadFail m) => B.MonadFail (ProgramT n m) where
  fail s = lift $ B.fail s

whenJust :: (Applicative m) => Maybe a -> (a -> m b) -> m (Maybe b)
whenJust Nothing _ = pure Nothing
whenJust (Just a) f = Just <$> f a

liftEither :: MonadError e m => Either e a -> m a
liftEither = either throwError pure

-- | Will modify an error if one is thrown, but otherwise leave it alone.
modifyError :: (MonadError e m) => (e -> e) -> m a -> m a
modifyError ef m = catchError m (throwError . ef)

-- | @'listens' f m@ is an action that executes the action @m@ and adds
-- the result of applying @f@ to the output to the value of the computation.
--
-- * @'listens' f m = 'liftM' (id *** f) ('listen' m)@
listens :: MonadWriter w m => (w -> b) -> m a -> m (a, b)
listens f m = do
    ~(a, w) <- listen m
    pure (a, f w)

-- | @'censor' f m@ is an action that executes the action @m@ and
-- applies the function @f@ to its output, leaving the return value
-- unchanged.
--
-- * @'censor' f m = 'pass' ('liftM' (\\x -> (x,f)) m)@
censor :: MonadWriter w m => (w -> w) -> m a -> m a
censor f m = pass $ do
    a <- m
    pure (a, f)

mappendMaybes :: (Monoid p) => [Maybe p] -> Maybe p
mappendMaybes = foldr mappendMaybe (Just mempty)

mappendMaybe :: (Semigroup p) => Maybe p -> Maybe p -> Maybe p
mappendMaybe a b = (<>) <$> a <*> b

-- | Generalization of `Maybe` to monads
maybeM :: (Monad m) => m a -> m (Maybe a) -> m a
maybeM d m = m >>= \case
  Just a -> pure a
  Nothing -> d

-- | perform some action if types don't match
matchType :: forall t t' a. (Typeable t)
           => TypeRep t' -> a -> (t :~~: t' -> a) -> a
matchType tr err succ = fromMaybe err $ do
  h <- eqTypeRep (typeRep @t) tr
  pure $ succ h

force :: forall b a c. (Newtype a c, Newtype b c) => a -> b
force = pack . unpack

-- | Matches a pair of types instead of just one.
matchType2 :: forall t m t' m' a. (Typeable t, Typeable m)
           => TypeRep t' -> a
           -> TypeRep m' -> a
           -> (t :~~: t' -> m :~~: m' -> a)
           -> a
matchType2 tt errt tm errm succ =
  matchType @t tt errt
    (\ rt -> matchType @m tm errm (\ rm -> succ rt rm))
{-
import Data.Functor as B

-- | This is a pair type meant mainly for syntax sugar, `key := val` is to be
--   read as "<key> is defined as <val>".
--
--   When bitraversed or bifolded over the value is evaluated before the key.
data a := b = a := b
  deriving(Show, Read, Eq, Ord, Typeable)
infixr 0 :=

instance B.Functor ((:=) a) where
  fmap f (a := b) = a := f b

instance Bifunctor (:=) where
  bimap f g (a := b) = f a := g b
  first f (a := b) = f a := b
  second g (a := b) = a := g b

instance Bifoldable (:=) where
  -- bitmap f g (a := b) = f a <> g b
  bifoldr f g d (a := b) = f a . g b $ d

instance Bitraversable (:=)

-- | This is the version of := where we know that the key has the same type as
--   the elements of the definition.
--
--   When traversed or folded over the value is changed before the key.
data f ::= a = a ::= (f a)
  deriving(Show, Read, Eq, Ord, Typeable)
infixr 0 ::=

instance Functor f => Functor ((::=) f) where
  fmap f (a ::= b) = f a ::= map f b

instance Foldable f => Foldable ((::=) f) where
  foldr f d (a ::= b) = f a (foldr f d b)

instance Traversable f => Traversable ((::=) f) where
  sequenceA (a ::= b) = flip (::=) <$> sequenceA b <*> a
-}


instance (Monoid w) => MFunctor (RWST r w s) where
    hoist nat m = rwsT (\r s -> nat (runRWST m r s))

instance (Monoid w) => MFunctor (WriterT w) where
    hoist nat m = writerT (nat (runWriterT m))
