{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language DeriveGeneric #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Class
( Permutable(..)
, Permutable1(..)
, Nominal(..)
, Nominal1(..)
, Stream(..)
, Fresh(..)
, Fresh1(..)
, fresh
-- , (#), support
, NominalSemigroup
, NominalMonoid
-- * Generics
, GPermutable, transgen, permgen
, GPermutable1
) where

import Control.Lens hiding (to, from, (#))
import qualified Data.Map.Internal as Map
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Generic
import Data.Proxy
import Data.Void
import GHC.Generics
import Nominal.Internal.Trie as Trie
import Nominal.Internal.Permutation
import Nominal.Set
import Nominal.Permutation
import Nominal.Support
import Nominal.Supported
import Nominal.Logic
import Prelude hiding (elem)

--------------------------------------------------------------------------------
-- * Permutable
--------------------------------------------------------------------------------

transgen :: (Generic s, GPermutable (Rep s)) => Atom -> Atom -> s -> s
transgen i j = to . gtrans i j . from
{-# inline [0] transgen #-}

permgen :: (Generic s, GPermutable (Rep s)) => Permutation -> s -> s
permgen p = to . gperm p . from
{-# inline [0] permgen #-}

{-# RULES
"transgen/transgen/ijij" [~1] forall i j x. transgen i j (transgen i j x) = x
"transgen/transgen/ijji" [~1] forall i j x. transgen i j (transgen j i x) = x
"permgen/swap=transgen" [~1] forall i j. permgen (swap i j) = transgen i j
"permgen/mempty=id" [~1] forall x. permgen (Permutation (Tree (Trie Map.Tip)) x) = id
  #-}

class Permutable s where
  trans :: Atom -> Atom -> s -> s
  default trans :: (Generic s, GPermutable (Rep s)) => Atom -> Atom -> s -> s
  trans = transgen
  {-# inline trans #-}

  -- |
  -- @
  -- perm mempty = id
  -- perm (p <> q) = perm p . perm q
  -- @
  perm :: Permutation -> s -> s
  default perm :: (Generic s, GPermutable (Rep s)) => Permutation -> s -> s
  perm = permgen
  {-# inline perm #-}

instance Permutable Atom where
  trans a b c
    | c == a = b
    | c == b = a
    | otherwise = c
  {-# inline trans #-}
  perm (Permutation t _) i = permTree t i
  {-# inline perm #-}

instance Permutable Permutation where
  trans a b t = swap a b <> t <> swap a b
  {-# inline trans #-}
  perm p t = p <> t <> inv p
  {-# inline perm #-}

instance Permutable Set where
  trans i j s = s
    & contains j .~ s^.contains i
    & contains i .~ s^.contains j
  {-# inline trans #-}
  perm (Permutation (Tree p) _) z = ifoldr tweak z p where
    tweak i j s = s & contains j .~ z^.contains i -- can't use trans, note s /= z
  {-# inline perm #-}

instance Permutable Support where
  trans i j (Supp s) = Supp $ s
    & at j .~ s^.at i
    & at i .~ s^.at j
  {-# inline trans #-}
  perm (Permutation (Tree p) _) (Supp z) = Supp $ ifoldr tweak z p where
    tweak i j s = s & at j .~ z^.at i
  {-# inline perm #-}

instance Permutable a => Permutable (Trie a) where
  trans i j s = s
    & at j .~ s^.at i
    & at i .~ s^.at j
  {-# inline trans #-}
  perm p0@(Permutation (Tree p) _) t = ifoldr tweak z p where
    tweak i j s = s & at j .~ z^.at i
    z = perm p0 <$> t
  {-# inline perm #-}

instance (Permutable a, Permutable b) => Permutable (a -> b) where
  trans a b f = trans a b . f . trans a b
  {-# inline trans #-}
  perm p f = perm p . f . perm (inv p)
  {-# inline perm #-}

instance Permutable Prop
instance (Permutable a, Permutable b) => Permutable (a, b)
instance (Permutable a, Permutable b, Permutable c) => Permutable (a, b, c)
instance (Permutable a, Permutable b, Permutable c, Permutable d) => Permutable (a, b, c, d)
instance (Permutable a, Permutable b) => Permutable (Either a b)
instance Permutable a => Permutable [a]
instance Permutable a => Permutable (Maybe a)
instance Permutable (Proxy a)
instance Permutable Void
instance Permutable ()
instance Permutable Bool
instance Permutable Int where
  trans _ _ = id
  {-# inline trans #-}
  perm _ = id
  {-# inline perm #-}
instance Permutable Word where
  trans _ _ = id
  {-# inline trans #-}
  perm _ = id
  {-# inline perm #-}

--------------------------------------------------------------------------------
-- * Permutable1
--------------------------------------------------------------------------------

transgen1 :: (Generic1 f, GPermutable1 (Rep1 f)) => (Atom -> Atom -> s -> s) -> Atom -> Atom -> f s -> f s
transgen1 f a b = to1 . gtrans1 f a b . from1
{-# inline [0] transgen1 #-}

permgen1 :: (Generic1 f, GPermutable1 (Rep1 f)) => (Permutation -> s -> s) -> Permutation -> f s -> f s
permgen1 f p = to1 . gperm1 f p . from1
{-# inline [0] permgen1 #-}

{-# RULES
"transgen1/transgen1/ijij" [~1] forall f i j x. transgen1 f i j (transgen1 f i j x) = x
"transgen1/transgen1/ijji" [~1] forall f i j x. transgen1 f i j (transgen1 f j i x) = x
"permgen1/swap=transgen1" [~1] forall f i j. permgen1 f (swap i j) = transgen1 (\x y -> f (swap x y)) i j
"permgen1/mempty=id" [~1] forall f x. permgen1 f (Permutation (Tree (Trie Map.Tip)) x) = id
  #-}

class Permutable1 f where
  trans1 :: (Atom -> Atom -> s -> s) -> Atom -> Atom -> f s -> f s
  default trans1 :: (Generic1 f, GPermutable1 (Rep1 f)) => (Atom -> Atom -> s -> s) -> Atom -> Atom -> f s -> f s
  trans1 = transgen1
  {-# inline trans1 #-}

  perm1 :: (Permutation -> s -> s) -> Permutation -> f s -> f s
  default perm1 :: (Generic1 f, GPermutable1 (Rep1 f)) => (Permutation -> s -> s) -> Permutation -> f s -> f s
  perm1 = permgen1
  {-# inline perm1 #-}

instance Permutable1 Proxy
instance Permutable1 []
instance Permutable1 Maybe
instance Permutable a => Permutable1 ((,)a)
instance (Permutable a, Permutable b) => Permutable1 ((,,) a b)
instance (Permutable a, Permutable b, Permutable c) => Permutable1 ((,,,) a b c)
instance Permutable a => Permutable1 (Either a)

instance Permutable1 Trie where
  trans1 f i j s = z
    & at j .~ z^.at i
    & at i .~ z^.at j
    where z = f i j <$> s
  {-# inline trans1 #-}
  perm1 f p0@(Permutation (Tree p) _) t = ifoldr tweak z p where
    tweak i j s = s & at j .~ z^.at i
    z = f p0 <$> t
  {-# inline perm1 #-}

--------------------------------------------------------------------------------
-- * Streams
--------------------------------------------------------------------------------

infixr 6 :-
data Stream = Atom :- Stream
  deriving Generic

instance Permutable Stream where
  trans i j (a :- as) = trans i j a :- trans i j as
  perm p (a :- as) = perm p a :- perm p as

--------------------------------------------------------------------------------
-- * Nominal
--------------------------------------------------------------------------------

sepgen :: Deciding Nominal s => Atom -> s -> Bool
sepgen a = getPredicate $ deciding (Proxy :: Proxy Nominal) (Predicate (a #))
{-# inline sepgen #-}

suppgen :: Deciding Nominal s => s -> Support
suppgen = getSupported $ deciding (Proxy :: Proxy Nominal) (Supported supp)
{-# inline suppgen #-}

equivgen :: Deciding Nominal s => s -> Atom -> Atom -> Bool
equivgen s i j = getPredicate (deciding (Proxy :: Proxy Nominal) (Predicate (\s' -> equiv s' i j))) s
{-# inline equivgen #-}

class Permutable s => Nominal s where

  -- @
  -- a # x = not (member a (supp b))
  -- @
  (#) :: Atom -> s -> Bool
  default (#) :: Deciding Nominal s => Atom -> s -> Bool
  (#) = sepgen
  {-# inline (#) #-}
  -- | The usual convention in nominal sets is to say something like:
  --
  -- @
  -- if (forall x in supp s. perm p x = x) then perm p s = s
  -- @
  --
  -- here,
  --
  -- @
  -- if (forall x in supp s. equiv (supp s) (perm p x) x) then perm p s = s
  -- @
  --
  -- This enables supports to describe allowed permutations.
  --
  -- Consider, a set of atoms, membership will return true given any atom in the set.
  -- but if you permuted those atoms that are within the set amongst themselves
  -- the answer wouldn't change. Similarly if you permuted elements that are solely
  -- outside of the set, the answer wouldn't change. It is only when you permute in
  -- such a way that exchanges elements from within the set with elements outside of
  -- the set that the answer fails to match
  supp :: s -> Support
  default supp :: Deciding Nominal s => s -> Support
  supp = suppgen
  {-# inline supp #-}

  supply :: s -> Stream
  supply (supp -> Supp s) = go $ maybe (A 0) (1+) $ sup s where
    go !i = i :- go (i+1)

  {-# inline supply #-}

  -- equivalent modulo support
  equiv :: s -> Atom -> Atom -> Bool
  default equiv :: Deciding Nominal s => s -> Atom -> Atom -> Bool
  equiv = equivgen
  {-# inline equiv #-}

instance Nominal Permutation where
  a # Permutation (Tree t) _ = not (Trie.member a t)
  supp (Permutation (Tree t) _) = Supp t
  equiv = equiv . supp

instance Nominal Support where
  a # Supp s = not (Trie.member a s)
  supp = id
  equiv (Supp s) i j = s^.at i == s^.at j

instance Nominal Atom where
  equiv a b c = (a == b) == (a == c)
  supply i = go 0 where
    go !j
      | i == j    = go (j+1)
      | otherwise = j :- go (j+1)
  (#) = (/=)
  supp a = Supp (Trie.singleton a ())

instance Nominal Set where
  a # s = not (Nominal.Set.member a s)
  supp (Set s) = Supp s
  equiv s i j = Nominal.Set.member i s == Nominal.Set.member j s

instance (Nominal a, Nominal b) => Nominal (a, b)
instance (Nominal a, Nominal b, Nominal c) => Nominal (a, b, c)
instance (Nominal a, Nominal b, Nominal c, Nominal d) => Nominal (a, b, c, d)
instance (Nominal a, Nominal b) => Nominal (Either a b)
instance Nominal a => Nominal [a]
instance Nominal a => Nominal (Maybe a)
instance Nominal (Proxy a)
instance Nominal Void where
  equiv = absurd
  supply = absurd
  supp  = absurd
  (#) _ = absurd

instance Nominal ()
instance Nominal Bool where
  equiv _ _ _ = True
instance Nominal Int where
  equiv _ _ _ = True
  _ # _ = True
  supp _ = mempty
instance Nominal Word where
  equiv _ _ _ = True
  _ # _ = True
  supp _ = mempty

--------------------------------------------------------------------------------
-- * Lifted Nominal Support
--------------------------------------------------------------------------------

class Permutable1 f => Nominal1 f where
  supp1 :: (s -> Support) -> f s -> Support
  default supp1 :: Deciding1 Nominal f => (s -> Support) -> f s -> Support
  supp1 f = getSupported $ deciding1 (Proxy :: Proxy Nominal) (Supported supp) (Supported f)

instance Nominal1 []
instance Nominal1 Maybe
instance Nominal1 Proxy
instance Nominal a => Nominal1 ((,) a)
instance (Nominal a, Nominal b) => Nominal1 ((,,) a b)
instance (Nominal a, Nominal b, Nominal c) => Nominal1 ((,,,) a b c)
instance Nominal a => Nominal1 (Either a)

-- (#) :: (Nominal a, Nominal b) => a -> b -> Bool
-- a # b = supp a `disjoint` supp b

--------------------------------------------------------------------------------
-- * Fresh
--------------------------------------------------------------------------------

class Fresh a where
  refresh :: Stream -> (a, Stream)

fresh :: (Nominal s, Fresh a) => s -> a
fresh = fst . refresh . supply

instance Fresh Atom where
  refresh (a :- as) = (a, as)

instance Fresh () where
  refresh = (,) ()

instance (Fresh a, Fresh b) => Fresh (a, b) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> ((a,b),cs)

instance (Fresh a, Fresh b, Fresh c) => Fresh (a, b, c) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case refresh cs of
        (c,ds) -> ((a,b,c),ds)

instance (Fresh a, Fresh b, Fresh c, Fresh d) => Fresh (a, b, c, d) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case refresh cs of
        (c,ds) -> case refresh ds of
          (d,es) -> ((a,b,c,d),es)

instance Fresh Stream where
  refresh as@(_ :- bs) = (skip as, skip bs) where
    skip (x :- _ :- xs) = x :- skip xs

--------------------------------------------------------------------------------
-- * Lifted Fresh
--------------------------------------------------------------------------------

class Fresh1 f where
  refresh1 :: (Stream -> (a, Stream)) -> Stream -> (f a, Stream)

instance Fresh a => Fresh1 ((,) a) where
  refresh1 f as = case refresh as of
    (a,bs) -> case f bs of
      (b,cs) -> ((a,b),cs)

instance (Fresh a, Fresh b) => Fresh1 ((,,) a b) where
  refresh1 f as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case f cs of
         (c,ds) -> ((a,b,c),ds)

instance (Fresh a, Fresh b, Fresh c) => Fresh1 ((,,,) a b c) where
  refresh1 f as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case refresh cs of
        (c,ds) -> case f ds of
          (d,es) -> ((a,b,c,d),es)

--------------------------------------------------------------------------------
-- * Nominal Semigroups
--------------------------------------------------------------------------------

-- | (<>) is a nominal morphism, @a@ is a semigroup in @Nom_fs@
--
-- This implies perm is a distributive group action
--
-- @
-- perm p (a <> b) = perm p a <> perm p b
-- supp (a <> b) ⊆ (supp a <> supp b)
-- @
--
class (Nominal a, Semigroup a) => NominalSemigroup a where
instance NominalSemigroup Set
instance NominalSemigroup Permutation

instance (NominalSemigroup a, NominalSemigroup b) => NominalSemigroup (a, b)
instance NominalSemigroup Support

--------------------------------------------------------------------------------
-- * Nominal Monoids
--------------------------------------------------------------------------------

-- | perm is a unital group action
--
-- @
-- perm p mempty = mempty
-- supp mempty = mempty -- mempty has empty support
-- @
class (NominalSemigroup a, Monoid a) => NominalMonoid a
instance NominalMonoid Permutation
instance NominalMonoid Set
instance (NominalMonoid a, NominalMonoid b) => NominalMonoid (a, b)

-- TODO: Nominal lattices, etc?

--------------------------------------------------------------------------------
-- * GHC Generics Support
--------------------------------------------------------------------------------

class GPermutable f where
  gtrans :: Atom -> Atom -> f a -> f a
  gperm :: Permutation -> f a -> f a

instance Permutable c => GPermutable (K1 i c) where
  gtrans i j (K1 a) = K1 (trans i j a)
  gperm p (K1 a) = K1 (perm p a)

instance GPermutable f => GPermutable (M1 i c f) where
  gtrans i j (M1 a) = M1 (gtrans i j a)
  gperm p (M1 a) = M1 (gperm p a)

instance GPermutable V1 where
  gtrans _ _ !v = case v of {}
  gperm _ !v = case v of {}

instance GPermutable U1 where
  gtrans _ _ U1 = U1
  gperm _ U1 = U1

instance (GPermutable f, GPermutable g) => GPermutable (f :*: g) where
  gtrans i j (a :*: b) = gtrans i j a :*: gtrans i j b
  gperm p (a :*: b) = gperm p a :*: gperm p b

instance (GPermutable f, GPermutable g) => GPermutable (f :+: g) where
  gtrans i j (L1 a) = L1 (gtrans i j a)
  gtrans i j (R1 a) = R1 (gtrans i j a)
  gperm p (L1 a) = L1 (gperm p a)
  gperm p (R1 a) = R1 (gperm p a)

instance (Permutable1 f, GPermutable g) => GPermutable (f :.: g) where
  gtrans i j (Comp1 a) = Comp1 (trans1 gtrans i j a)
  gperm p (Comp1 a) = Comp1 (perm1 gperm p a)

class GPermutable1 f where
  gtrans1 :: (Atom -> Atom -> a -> a) -> Atom -> Atom -> f a -> f a
  gperm1 :: (Permutation -> a -> a) -> Permutation -> f a -> f a

instance Permutable c => GPermutable1 (K1 i c) where
  gtrans1 _ i j (K1 a) = K1 (trans i j a)
  gperm1 _ p (K1 a) = K1 (perm p a)

instance GPermutable1 f => GPermutable1 (M1 i c f) where
  gtrans1 f i j (M1 a) = M1 (gtrans1 f i j a)
  gperm1 f p (M1 a) = M1 (gperm1 f p a)

instance GPermutable1 V1 where
  gtrans1 _ _ _ !v = case v of {}
  gperm1 _ _ !v = case v of {}

instance GPermutable1 U1 where
  gtrans1 _ _ _ U1 = U1
  gperm1 _ _ U1 = U1

instance (GPermutable1 f, GPermutable1 g) => GPermutable1 (f :*: g) where
  gtrans1 f i j (a :*: b) = gtrans1 f i j a :*: gtrans1 f i j b
  gperm1 f p (a :*: b) = gperm1 f p a :*: gperm1 f p b

instance (GPermutable1 f, GPermutable1 g) => GPermutable1 (f :+: g) where
  gtrans1 f i j (L1 a) = L1 (gtrans1 f i j a)
  gtrans1 f i j (R1 a) = R1 (gtrans1 f i j a)
  gperm1 f p (L1 a) = L1 (gperm1 f p a)
  gperm1 f p (R1 a) = R1 (gperm1 f p a)

instance (Permutable1 f, GPermutable1 g) => GPermutable1 (f :.: g) where
  gtrans1 f i j (Comp1 a) = Comp1 (trans1 (gtrans1 f) i j a)
  gperm1 f p (Comp1 a) = Comp1 (perm1 (gperm1 f) p a)

instance GPermutable1 Par1 where
  gtrans1 f i j (Par1 a) = Par1 (f i j a)
  gperm1 f p (Par1 a) = Par1 (f p a)

instance Permutable1 f => GPermutable1 (Rec1 f) where
  gtrans1 f i j (Rec1 a) = Rec1 (trans1 f i j a)
  gperm1 f p (Rec1 a) = Rec1 (perm1 f p a)
