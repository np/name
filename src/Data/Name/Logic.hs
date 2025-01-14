{-# language LambdaCase #-}
{-# language DeriveGeneric #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}
{-# language BangPatterns #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Logic
( Prop(..)
, neg, implies, iff, top
, liftB, liftB2
) where

import Control.Lens
import Data.Semigroup
import GHC.Generics
import Data.Name.Lattice
import Data.Name.Internal.Fun
import Data.Name.Set
import Data.Name.Type (Name)
import Data.Name.Class

-- TODO: check my back of the envelope math

-- the finite-cofinite algebra on atoms
-- this satisfies excluded-middle, etc.
data Prop n = Finite (Set n) | Cofinite (Set n) deriving (Generic, Eq)

instance IsNameRepr n => Permutable n (Prop n)
instance IsNameRepr n => Nominal n (Prop n)

instance IsNameRepr n => Semigroup (Prop n)  where
  stimes n m = case compare n 0 of
    LT -> neg m
    EQ -> mempty
    GT -> m
  {-# inline stimes #-}

  Finite p   <> Finite q   = Finite   (p ∨ q)
  Finite p   <> Cofinite q = Finite   (q \\ p)
  Cofinite p <> Finite q   = Finite   (p \\ q)
  Cofinite p <> Cofinite q = Cofinite (p ∧ q)
  {-# inline (<>) #-}

instance IsNameRepr n => Monoid (Prop n) where
  mempty = Finite mempty

instance IsNameRepr n => Join (Prop n)
instance IsNameRepr n => BoundedJoin (Prop n)

instance IsNameRepr n => Meet (Prop n) where
  Finite p   ∧ Finite q   = Finite   (p ∧ q) -- pq
  Finite p   ∧ Cofinite q = Finite   (p \\ q) -- p(S-q)=pS-pq=p-q
  Cofinite p ∧ Finite q   = Finite   (q \\ p) -- (S-p)q=Sq-pq=q-pq=q-p
  Cofinite p ∧ Cofinite q = Cofinite (p ∨ q)
  -- (S-p)(S-q)=S(S-q)-p(S-q)=SS-Sq-pS-pq=S-q-p-pq=S-q-p=S-(q+p)
  {-# inline (∧) #-}

instance IsNameRepr n => DistributiveLattice (Prop n)

instance IsNameRepr n => GBA (Prop n) where
  -- nominal
  -- @p \\ q = p ∧ neg q@
  Finite p   \\ Finite q   = Finite   (p \\ q)
  Finite p   \\ Cofinite q = Finite   (p ∧ q)
  Cofinite p \\ Finite q   = Cofinite (p ∨ q)
  Cofinite p \\ Cofinite q = Finite   (q \\ p)
  {-# inline (\\) #-}

  -- nominal
  xor (Finite p) (Cofinite q)   = Cofinite (p ∧ q)
  xor (Cofinite p) (Finite q)   = Cofinite (p ∧ q)
  xor (Finite p) (Finite q)     = Finite  (xor p q)
  xor (Cofinite p) (Cofinite q) = Finite  (xor p q)
  {-# inline xor #-}

-- nominal
instance IsNameRepr n => SetLike (Prop n) where
  member a (Finite s)   = member a s
  member a (Cofinite s) = not (member a s)
  {-# inline member #-}

  -- nominal
  insert a (Finite s)   = Finite (insert a s)
  insert a (Cofinite s) = Cofinite (delete a s)
  {-# inline insert #-}

  singleton = Finite . singleton
  {-# inline singleton #-}

  delete a (Finite s)   = Finite (delete a s)
  delete a (Cofinite s) = Cofinite (insert a s)
  {-# inline delete #-}

instance IsNameRepr n => BoundedMeet (Prop n) where
  top = Cofinite bottom
  {-# inline conlike top #-}

instance IsNameRepr n => Boolean (Prop n) where
  neg (Finite s) = Cofinite s
  neg (Cofinite s) = Finite s
  {-# inline neg #-}

  implies (Finite p) (Finite q)     = Finite   (p \\ q)
  implies (Finite p) (Cofinite q)   = Cofinite (p ∧ q)
  implies (Cofinite p) (Finite q)   = Finite   (p ∨ q)
  implies (Cofinite p) (Cofinite q) = Finite   (q \\ p)
  {-# inline implies #-}

  iff (Finite p)   (Finite q)   = Cofinite (xor p q)
  iff (Finite p)   (Cofinite q) = Finite   (p ∧ q)
  iff (Cofinite p) (Cofinite q) = Cofinite (xor p q)
  iff (Cofinite p) (Finite q)   = Finite   (p ∧ q)
  {-# inline iff #-}

-- instance NominalSemigroup (Prop n)
-- instance NominalMonoid (Prop n)

instance IsNameRepr n => AsEmpty (Prop n) where
  _Empty = prism (const (Finite mempty)) $ \case
     Finite Empty -> Right ()
     t -> Left t
  {-# inline _Empty #-}

type instance Index (Prop n) = Name n
instance IsNameRepr n => Contains (Prop n) where
  contains a f (Finite s) = Finite <$> contains a f s
  contains a f (Cofinite s) = Cofinite <$> contains a (fmap not . f . not) s
  {-# inline contains #-}

-- lift a unary boolean function
liftB :: IsNameRepr n => (Bool -> Bool) -> Prop n -> Prop n
liftB f !s
  | f False   = if f True then top else neg s
  | otherwise = if f True then s else bottom

table :: IsNameRepr n => Fun -> Prop n -> Prop n -> Prop n
table TNever  _ _ = bottom
table TAnd    f g = f ∧ g
table TGt     f g = f \\ g -- f > g
table TF      f _ = f
table TLt     f g = g \\ f -- f < g
table TG      _ g = g
table TXor    f g = xor f g
table TOr     f g = f ∨ g -- f || g
table TNor    f g = neg f ∧ neg g -- nor f g
table TXnor   f g = iff f g -- f ∧ g ∨ neg f ∧ neg g
table TG'     _ g = neg g
table TGe     f g = implies g f -- f ∧ neg g  -- f >= g
table TF'     f _ = neg f
table TLe     f g = implies f g -- ite f g One        -- f <= g
table TNand   f g = neg (f ∧ g) -- ite f (neg g) One  -- nand f g
table TAlways _ _ = top

-- | lift boolean functions through the table e.g. @liftB2 (&&)@, @liftB2 (<=)@
liftB2 :: IsNameRepr n => (Bool -> Bool -> Bool) -> Prop n -> Prop n -> Prop n
liftB2 = table . fun

-- instance Bits (Prop n)

-- TODO: instance PartialOrder (Prop n) where
