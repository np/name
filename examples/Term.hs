{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language TypeOperators #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language StandaloneDeriving #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Term where

import Control.Lens
import GHC.Generics
import Data.Name
import Data.Name.Natural
import qualified Data.Name.Map as Map
import Debug.Trace (trace)

-- Eq automatically respects alpha-equivalence of bound terms

data Term n
  = Var !(Name n)
  | App !(Term n) !(Term n)
  | Lam !(Tie n (Name n) (Term n))
  | NotVar !(Name n)
  deriving (Eq, Show, Generic)
  
deriving instance IsNameRepr n => Permutable n (Term n)
deriving instance IsNameRepr n => Nominal n (Term n)

instance IsNameRepr n => Subst n (Term n) (Name n) where
  -- Ok if there are no other occurrences of `Name n` in `Term n` than `Var` and `Tie`.
  -- subst _ _ = id
  -- Otherwise this at leasts permutes
  subst _ = perm

instance IsNameRepr n => AsName n (Term n) where
  _Name = prism Var $ \case
    Var v -> Right v
    x -> Left x

substTerm :: (IsNameRepr n, Enum n) => Map n (Term n) -> Permutation n -> Term n -> Term n
substTerm = subst 

betaReduce :: (Enum n, IsNameRepr n) => Term n -> Term n
betaReduce (App (Lam (Tie x t)) u) = substTerm (Map.singleton x u) mempty t
betaReduce t = t

test :: [String]
test =
  let a = NameRepr (1 :: NatNameRepr)
      b = NameRepr 2
      c = NameRepr 2
      lamaa = Lam (Tie a (Var a))
      lambb = Lam (Tie b (Var b))
      const_ = Lam (Tie a (Lam (Tie b (Var a))))
      check (x, y) =
        case (sx == sy, x == y) of
          (True,  True)  -> "identical"
          (True,  False) -> trace sx (trace sy "ERROR")
          (False, True)  -> "equiv"
          (False, False) -> trace sx (trace sy "different")
        where
          sx = show x
          sy = show y
  in
  check <$>
  [ (lamaa, lambb)
  , (trans a b (NotVar a), NotVar b)
  , (substTerm Map.empty (swap a b) (NotVar a), NotVar b)
  , (betaReduce (App lamaa lambb), lambb)
  , (betaReduce (App lamaa lamaa), lamaa)
  , (betaReduce (App const_ lamaa), Lam (Tie b lamaa))
  , (betaReduce (App const_ lambb), Lam (Tie b lambb))
  , (betaReduce (App const_ (Var a)), Lam (Tie c (Var a)))
  ]