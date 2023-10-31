{-# language TypeFamilies #-}
{-# language FlexibleContexts #-}
{-# language LambdaCase #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Permutation
( Permutation(..)
, swap -- generator
, rcycles, cycles, cyclic, reassemble -- traditional presentation
, inv -- invert a permutation
, parity
, sign
, conjugacyClass
) where

import Control.Lens
import Control.Monad
import Data.Bits
import Data.List (groupBy, sort)
import Data.Name.Internal.Perm
import Data.Name.Internal.Trie
import Data.Name.Internal.IsNameRepr
import Data.Semigroup
import Prelude hiding (elem, lookup)
import Data.Name.Type (Name (..))
import Data.Function (on)

-- | The pair of a permutation and its inverse permutation
data Permutation n = Permutation (Perm n) (Perm n)
  deriving Show

instance Eq n => Eq (Permutation n) where
  Permutation x _ == Permutation y _ = x == y

{- See remark in Data.Name.Internal.Perm

instance Ord n => Ord (Permutation n) where
  Permutation x _ `compare` Permutation y _ = compare x y
-}

instance IsNameRepr n => AsEmpty (Permutation n) where
  _Empty = prism (const mempty) $ \case
    Permutation (Perm Empty) _ -> Right ()
    t -> Left t

inv :: Permutation n -> Permutation n
inv (Permutation s t) = Permutation t s

square :: IsNameRepr n => Permutation n -> Permutation n
square (Permutation s t) = Permutation (square' s) (square' t)

instance IsNameRepr n => Semigroup (Permutation n) where
  Permutation a b <> Permutation c d = Permutation (a <> c) (d <> b)
  stimes n x0 = case compare n 0 of
    LT -> f (inv x0) (negate n)
    EQ -> mempty
    GT -> f x0 n
    where
      f x y
        | even y = f (square x) (quot y 2)
        | y == 1 = x
        | otherwise = g (square x) (quot y 2) x
      g x y z
        | even y = g (square x) (quot y 2) z
        | y == 1 = x <> z
        | otherwise = g (square x) (quot y 2) (x <> z)

instance IsNameRepr n => Monoid (Permutation n) where
  mempty = Permutation mempty mempty

-- promote :: Perm n -> Permutation n
-- promote t = Permutation t (inv' t)

-- | equivariant
swap :: IsNameRepr n => Name n -> Name n -> Permutation n
swap i j
  | i /= j = join Permutation $ Perm $ insert i (_nameRepr j) $ insert j (_nameRepr i) Empty
  | otherwise = mempty
{-# inline [0] swap #-}

-- | This is not quite natural order, as its easiest for me to find the largest element and work backwards.
-- for natural order, reverse the list of cycles. Not a nominal arrow
rcycles :: IsNameRepr n => Permutation n -> [[Name n]]
rcycles (Permutation t0 _) = go t0 where
  go t = case sup' t of
    Nothing -> []
    Just m -> case peel m m t of
      (t',xs) -> xs : go t'

  -- mangles the tree to remove this cycle as we go
  peel :: IsNameRepr n => Name n -> Name n -> Perm n -> (Perm n, [Name n])
  peel m e (Perm t) = case lookup e t of
    Nothing -> error $ show (m,e,t)
    Just n | NameRepr n == m -> (Perm (delete e t), [e])
           | otherwise -> (e:) <$> peel m (NameRepr n) (Perm (delete e t))

-- | standard cyclic representation of a permutation, broken into parts. Not equivariant
cycles :: IsNameRepr n => Permutation n -> [[Name n]]
cycles = reverse . rcycles

-- | standard cyclic representation of a permutation, smashed flat. Not equivariant
cyclic :: IsNameRepr n => Permutation n -> [Name n]
cyclic = concat . cycles

-- | If the conjugacy class of two permutations is the same then there is a permutation that
-- can be used to conjugate one to get the other. equivariant
--
-- @
-- 'conjugacyClass' x ≡ 'conjugacyClass' y => ∃z, y = z <> x <> inv z
-- 'perm' p 'conjugacyClass' q = 'conjugacyClass' ('perm' p q) = 'conjugacyClass' q
-- @
conjugacyClass :: IsNameRepr n => Permutation n -> [Int]
conjugacyClass = sort . map length . rcycles

-- | Reassemble takes a standard cyclic representation smashed flat and reassembles the cycles, not equivariant
--
-- @
-- 'reassemble' . 'cyclic' = 'cycles'
-- 'concat' . 'reassemble' = 'id'
-- 'perm' p . 'reassemble' = 'reassemble' . 'perm' p
-- @
--
-- TODO move to Data.Name.Type?
reassemble :: Ord n => [Name n] -> [[Name n]]
reassemble = groupBy ((>) `on` _nameRepr)

-- | Equivariant
-- 
-- @
-- 'perm' p 'parity' q = perm p ('parity' p ('perm' (inv p) q)) = 'parity' q
-- @
parity :: IsNameRepr n => Permutation n -> Bool
parity = foldr (xor . foldr (const not) True) True . rcycles

-- | Determinant of the permutation matrix, equivariant
sign :: IsNameRepr n => Permutation n -> Int
sign g = (-1) ^ fromEnum (parity g)
