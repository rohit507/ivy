
module Scratchpad where

import Intro hiding (Const)

data Lit c f where
  Lit :: c -> Lit c f

data Op c f where
  Add :: Either (f (Lit c)) (f (Op c)) -> f (Op c) -> Op c f
  Mul :: Either (f (Lit c)) (f (Op c)) -> f (Op c) -> Op c f

data Term v t where
  Term :: t (Term v) -> Term v t
  Var  :: v -> Term v t

foo :: (Eq v, Num n) => v ->  n -> Term v (Op n)
foo v n = Term $ Add (Left $ Lit n) (Var v)
