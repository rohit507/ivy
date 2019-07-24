
{-# LANGUAGE AllowAmbiguousTypes #-}
{-|
Module      : Ivy.Scratchpad
Description : Random scratch work goes here until it's moved
Copyright   : (c) Rohit Ramesh, 2018
License     : GPL-2
Maintainer  : rkr@berkley.edu
Stability   : experimental
Portability : POSIX

A pile of instances of `Newtype * Int` that we use to differentiate Idents
used for different purposes.
-}

module Ivy.Wrappers.IDs where

import Ivy.Prelude
import Ivy.MonadClasses

-- | A termID without knowledge about the type of its term.
newtype ETermID = ETID { getETID :: Int }
  deriving (Eq, Ord, Show, Generic, Hashable)
type ETID = ETermID


instance Newtype ETermID Int where
  pack = ETID
  unpack = getETID

-- | an identifier for a specific term.
newtype TermID t = TermID { getTID :: Int }
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Newtype (TermID t) Int where
  pack = TermID
  unpack = getTID

type TID = TermID

-- | an identifier for a specific term.
newtype VarID t m = VID { getVID :: Int}
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Newtype (VarID t m) Int where
  pack = VID
  unpack = getVID

newtype RuleID = RuleID { getRID :: Int}
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Newtype RuleID Int where
  pack = RuleID
  unpack = getRID


-- | Strip type information from a TermID
crushTID :: TermID t -> ETermID
crushTID = pack . unpack

-- | Add (potentially incorrect) type information to am ETID
unsafeExpandTID :: ETermID -> TermID t
unsafeExpandTID = pack . unpack

-- | Strip Monad information from a VerID
crushVID :: VarID t m -> TermID t
crushVID = pack . unpack

flattenVID :: VarID t m -> ETID
flattenVID = crushTID . crushVID

-- | Add (potentially incorrect) monad information to a VID
unpackVID :: forall m t. TermID t -> VarID t m
unpackVID = pack . unpack

typedTID :: forall t e. (Term e t) => TermID t -> TypedVar
typedTID tid = TVar (typeRep @t) (typeRep @e) tid

typedVID :: forall t m e. (Term e t) => VarID t m -> TypedVar
typedVID vid = typedTID @t @e $ crushVID vid

getTypedTID :: forall t e. (Term e t) => TypedVar -> Maybe (TermID t)
getTypedTID (TVar tt te t) = do
  HRefl <- eqTypeRep tt (typeRep @t)
  HRefl <- eqTypeRep te (typeRep @e)
  pure t

getTypedVID :: forall t m e. (Term e t, MonadError e m)
            => TypedVar -> Maybe (VarID t m)
getTypedVID tvar = unpackVID @m @t <$> getTypedTID @t @e tvar


type TVar = TypedVar

data TypedVar where
  TVar :: (Term e t)
    => TypeRep t
    -> TypeRep e
    -> TermID t
    -> TypedVar

instance Ord TypedVar where
  compare (TVar _ _ n) (TVar _ _ n') = compare (unpack n) (unpack n')

instance Eq TypedVar where
  (TVar tt te v) == (TVar tt' te' v') = fromMaybe False $ do
    HRefl <- eqTypeRep tt tt'
    HRefl <- eqTypeRep te te'
    pure $ v == v'

instance Hashable TypedVar where
  hashWithSalt s (TVar _ _ n) = hashWithSalt s (unpack n)
