{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
{-# language ViewPatterns #-}
{-# language DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Class
( IsName()
, AsName(..)
, HasName(..)
, Permutable(..), Permutable1(..)
, Nominal(..), Nominal1(..)
, Basic, Basic1
, Supply(..), suppgen, equivgen, sepgen, supplysupp, supplygen
, Fresh(..), Fresh1(..), fresh
-- , (#), support
, NominalSemigroup, NominalMonoid
-- * Generics
, GPermutable, GPermutable1, transgen, permgen
-- * Binding
, Binding(..), Binding1(..)
, Irrefutable(..), Irrefutable1(..)
-- * Internals
, Supported(..)
, Binder(..)
) where

import Control.Monad
import Control.Lens hiding (to, from, (#))
import Data.Coerce
import Data.Discrimination.Grouping
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.Contravariant.Generic
import qualified Data.Map.Internal as Map
import Data.Name.Type (Name(..))
import Data.Name.Internal.Trie as Trie
import Data.Name.Internal.Perm
import Data.Name.Set as Set
import Data.Name.Permutation
import Data.Name.Support
import Data.Proxy
import Data.Void
import GHC.Generics
import Prelude hiding (elem)
import Data.Name.Internal.IsName (IsName)

--------------------------------------------------------------------------------
-- * IsName
--------------------------------------------------------------------------------

class IsName n => AsName n t where
  _Name :: Prism' t (Name n)

instance IsName n => AsName n (Name n) where
  _Name = id

instance AsName n a => AsName n (Maybe a) where
  _Name = _Just._Name

--------------------------------------------------------------------------------
-- * HasName
--------------------------------------------------------------------------------

class IsName n => HasName n t where
  nameOf :: Lens' t (Name n)

instance IsName n => HasName n (Name n) where
  nameOf = id

--------------------------------------------------------------------------------
-- * Permutable
--------------------------------------------------------------------------------

transgen :: (Generic s, GPermutable n (Rep s)) => Name n -> Name n -> s -> s
transgen i j = to . gtrans i j . from
{-# inline [0] transgen #-}

permgen :: (Generic s, GPermutable n (Rep s)) => Permutation n -> s -> s
permgen p = to . gperm p . from
{-# inline [0] permgen #-}

{-# RULES
"transgen/transgen/ijij" [~1] forall i j x. transgen i j (transgen i j x) = x
"transgen/transgen/ijji" [~1] forall i j x. transgen i j (transgen j i x) = x
"permgen/swap=transgen" [~1] forall i j. permgen (swap i j) = transgen i j
"permgen/mempty=id" [~1] forall x. permgen (Permutation (Perm (Trie Map.Tip)) x) = id
  #-}

class IsName n => Permutable n s where
  trans :: Name n -> Name n -> s -> s
  default trans :: (Generic s, GPermutable n (Rep s)) => Name n -> Name n -> s -> s
  trans = transgen
  {-# inline trans #-}

  -- |
  -- @
  -- perm mempty = id
  -- perm (p <> q) = perm p . perm q
  -- @
  perm :: Permutation n -> s -> s
  default perm :: (Generic s, GPermutable n (Rep s)) => Permutation n -> s -> s
  perm = permgen
  {-# inline perm #-}

instance IsName n => Permutable n (Name n) where
  trans a b c
    | c == a = b
    | c == b = a
    | otherwise = c
  {-# inline trans #-}
  perm (Permutation t _) = perm' t

  {-# inline perm #-}

instance IsName n => Permutable n (Permutation n) where
  trans a b t = swap a b <> t <> swap a b
  {-# inline trans #-}
  perm p t = p <> t <> inv p
  {-# inline perm #-}

instance IsName n => Permutable n (Set n) where
  trans i j s = s
    & contains j .~ s^.contains i
    & contains i .~ s^.contains j
  {-# inline trans #-}
  perm (Permutation (Perm p) _) z = ifoldr tweak z p where
    tweak i j s = s & contains (NameRepr j) .~ z^.contains i -- can't use trans, note s /= z
  {-# inline perm #-}

instance IsName n => Permutable n (Support n) where
  trans i j (Supp s) = Supp $ s
    & at j .~ s^.at i
    & at i .~ s^.at j
  {-# inline trans #-}
  perm (Permutation (Perm p) _) (Supp z) = Supp $ ifoldr tweak z p where
    tweak i j s = s & at (NameRepr j) .~ z^.at i
  {-# inline perm #-}

instance Permutable n a => Permutable n (Trie n a) where
  trans i j s = s
    & at j .~ s^.at i
    & at i .~ s^.at j
  {-# inline trans #-}
  perm p0@(Permutation (Perm p) _) t = ifoldr tweak z p where
    tweak i j s = s & at (NameRepr j) .~ z^.at i
    z = perm p0 <$> t
  {-# inline perm #-}

instance (Permutable n a, Permutable n b) => Permutable n (a -> b) where
  trans a b f = trans a b . f . trans a b
  {-# inline trans #-}
  perm p f = perm p . f . perm (inv p)
  {-# inline perm #-}

instance (Permutable n a, Permutable n b) => Permutable n (a, b)
instance (Permutable n a, Permutable n b, Permutable n c) => Permutable n (a, b, c)
instance (Permutable n a, Permutable n b, Permutable n c, Permutable n d) => Permutable n (a, b, c, d)
instance (Permutable n a, Permutable n b) => Permutable n (Either a b)
instance Permutable n a => Permutable n [a]
instance Permutable n a => Permutable n (Maybe a)
instance IsName n => Permutable n (Proxy a)
instance IsName n => Permutable n Void
instance IsName n => Permutable n ()
instance IsName n => Permutable n Bool
instance IsName n => Permutable n Char where
  trans _ _ = id
  {-# inline trans #-}
  perm _ = id
  {-# inline perm #-}
instance IsName n => Permutable n Int where
  trans _ _ = id
  {-# inline trans #-}
  perm _ = id
  {-# inline perm #-}
instance IsName n => Permutable n Word where
  trans _ _ = id
  {-# inline trans #-}
  perm _ = id
  {-# inline perm #-}

--------------------------------------------------------------------------------
-- * Permutable1
--------------------------------------------------------------------------------

transgen1 :: (Generic1 f, GPermutable1 n (Rep1 f)) => (Name n -> Name n -> a -> b) -> Name n -> Name n -> f a -> f b
transgen1 f a b = to1 . gtrans1 f a b . from1
{-# inline [0] transgen1 #-}

permgen1 :: (Generic1 f, GPermutable1 n (Rep1 f)) => (Permutation n -> a -> b) -> Permutation n -> f a -> f b
permgen1 f p = to1 . gperm1 f p . from1
{-# inline [0] permgen1 #-}

defaultFmap :: forall proxy n f a b. (IsName n, Permutable1 n f) => proxy n -> (a -> b) -> f a -> f b
defaultFmap _ f = perm1 (const f) (mempty :: Permutation n)

{-# RULES
"transgen1/transgen1/ijij" [~1] forall f i j x. transgen1 f i j (transgen1 f i j x) = x
"transgen1/transgen1/ijji" [~1] forall f i j x. transgen1 f i j (transgen1 f j i x) = x
"permgen1/swap=transgen1" [~1] forall f i j. permgen1 f (swap i j) = transgen1 (\x y -> f (swap x y)) i j
"permgen1/mempty=id" [~1] forall f x. permgen1 f (Permutation (Perm (Trie Map.Tip)) x) = id
  #-}

-- Could also be called PermutableFunctor
class (IsName n, Functor f) => Permutable1 n f where
  trans1 :: (Name n -> Name n -> a -> b) -> Name n -> Name n -> f a -> f b
  default trans1 :: (Generic1 f, GPermutable1 n (Rep1 f)) => (Name n -> Name n -> a -> b) -> Name n -> Name n -> f a -> f b
  trans1 = transgen1
  {-# inline trans1 #-}

  perm1 :: (Permutation n -> a -> b) -> Permutation n -> f a -> f b
  default perm1 :: (Generic1 f, GPermutable1 n (Rep1 f)) => (Permutation n -> a -> b) -> Permutation n -> f a -> f b
  perm1 = permgen1
  {-# inline perm1 #-}

instance IsName n => Permutable1 n Proxy
instance IsName n => Permutable1 n []
instance IsName n => Permutable1 n Maybe
instance Permutable n a => Permutable1 n ((,)a)
instance (Permutable n a, Permutable n b) => Permutable1 n ((,,) a b)
instance (Permutable n a, Permutable n b, Permutable n c) => Permutable1 n ((,,,) a b c)
instance Permutable n a => Permutable1 n (Either a)

instance IsName n => Permutable1 n (Trie n) where
  trans1 f i j s = z
    & at j .~ z^.at i
    & at i .~ z^.at j
    where z = f i j <$> s
  {-# inline trans1 #-}
  perm1 f p0@(Permutation (Perm p) _) t = ifoldr tweak z p where
    tweak i j s = s & at (NameRepr j) .~ z^.at i
    z = f p0 <$> t
  {-# inline perm1 #-}

--------------------------------------------------------------------------------
-- * Supplys
--------------------------------------------------------------------------------

newtype Supply n = Supply {getSupply :: n} deriving Generic

instance Ord n => Semigroup (Supply n) where
  Supply a <> Supply b = Supply (max a b)

instance (IsName n, Enum n) => Monoid (Supply n) where
  mempty = Supply (toEnum 0)

{-
instance Permutable (Supply n) where
  trans i j (a :- as) = trans i j a :- trans i j as
  perm p (a :- as) = perm p a :- perm p as
-}

--------------------------------------------------------------------------------
-- * Supported
--------------------------------------------------------------------------------

newtype Supported n a = Supported { getSupported :: a -> Support n }

instance Contravariant (Supported n) where
  contramap f (Supported g) = Supported (g . f)

instance IsName n => Divisible (Supported n) where
  conquer = Supported $ \_ -> mempty
  divide f (Supported g) (Supported h) = Supported $ \a -> case f a of
    (b, c) -> g b <> h c

instance IsName n => Decidable (Supported n) where
  lose f = Supported $ absurd . f
  choose f (Supported g) (Supported h) = Supported $ \a -> case f a of
    Left b -> g b
    Right c -> h c

--------------------------------------------------------------------------------
-- * Nominal
--------------------------------------------------------------------------------

sepgen :: forall n s. Deciding (Nominal n) s => Name n -> s -> Bool
sepgen a = getPredicate $ deciding (Proxy :: Proxy (Nominal n)) (Predicate (a #))
{-# inline sepgen #-}

suppgen :: forall n s. (IsName n, Deciding (Nominal n) s) => s -> Support n
suppgen = getSupported $ deciding (Proxy :: Proxy (Nominal n)) (Supported supp)
{-# inline suppgen #-}

equivgen :: forall n s. Deciding (Nominal n) s => s -> Name n -> Name n -> Bool
equivgen s i j = getPredicate (deciding (Proxy :: Proxy (Nominal n)) (Predicate (\s' -> equiv s' i j))) s
{-# inline equivgen #-}

supplygen :: forall n s. (IsName n, Enum n, Deciding (Nominal n) s) => s -> Supply n
supplygen = getOp $ deciding (Proxy :: Proxy (Nominal n)) (Op supply)

-- fast if you have O(1) support
supplysupp :: Enum n => Nominal n s => s -> Supply n
supplysupp (supp -> Supp s) = Supply . maybe (toEnum 0) (succ . _nameRepr) $ sup s

class Permutable n s => Nominal n s where

  -- @
  -- a # x = not (member a (supp b))
  -- @
  (#) :: Name n -> s -> Bool
  default (#) :: Deciding (Nominal n) s => Name n -> s -> Bool
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
  supp :: s -> Support n
  default supp :: Deciding (Nominal n) s => s -> Support n
  supp = suppgen
  {-# inline supp #-}

  supply :: Enum n => s -> Supply n
  default supply :: (Enum n, Deciding (Nominal n) s) => s -> Supply n
  supply = supplygen
  {-# inline supply #-}

  -- equivalent modulo support
  equiv :: s -> Name n -> Name n -> Bool
  default equiv :: Deciding (Nominal n) s => s -> Name n -> Name n -> Bool
  equiv = equivgen
  {-# inline equiv #-}

instance IsName n => Nominal n (Permutation n) where
  a # Permutation (Perm t) _ = not (Trie.member a t)
  supp (Permutation (Perm t) _) = Supp t
  supply = supplysupp
  equiv π = equiv (supp π :: Support n)

instance IsName n => Nominal n (Support n) where
  a # Supp s = not (Trie.member a s)
  supp = id
  supply = supplysupp
  equiv (Supp s) i j = s^.at i == s^.at j

instance IsName n => Nominal n (Name n) where
  equiv a b c = (a == b) == (a == c)
  supply (NameRepr i) = Supply $ succ i
  (#) = (/=)
  supp n = Supp (Trie.singleton n ())

newtype Blind a = Blind a
instance Eq (Blind a) where _ == _ = True
instance Ord (Blind a) where compare _ _ = EQ
instance Grouping (Blind a) where grouping = conquer

instance IsName n => Nominal n (Set n) where
  a # s = not (Set.member a s)
  supply = supplysupp
  supp (Set s) = Supp (go s) where
    go :: Trie n a -> Trie n (Blind a)
    go = coerce
    _ignore :: a -> Blind a
    _ignore = Blind

  equiv s i j = Set.member i s == Set.member j s

instance (Nominal n a, Nominal n b) => Nominal n (a, b)
instance (Nominal n a, Nominal n b, Nominal n c) => Nominal n (a, b, c)
instance (Nominal n a, Nominal n b, Nominal n c, Nominal n d) => Nominal n (a, b, c, d)
instance (Nominal n a, Nominal n b) => Nominal n (Either a b)
instance Nominal n a => Nominal n [a]
instance Nominal n a => Nominal n (Maybe a)
instance IsName n => Nominal n (Proxy a)
instance IsName n => Nominal n Void where
  equiv = absurd
  supply = absurd
  supp  = absurd
  (#) _ = absurd

instance IsName n => Nominal n ()

instance IsName n => Nominal n Bool where
  equiv _ _ _ = True

instance IsName n => Nominal n Int where
  equiv _ _ _ = True
  _ # _ = True
  supp _ = mempty
  supply _ = mempty

instance IsName n => Nominal n Char where
  equiv _ _ _ = True
  _ # _ = True
  supp _ = mempty
  supply _ = mempty

instance IsName n => Nominal n Word where
  equiv _ _ _ = True
  _ # _ = True
  supp _ = mempty
  supply _ = mempty

--------------------------------------------------------------------------------
-- * Lifted Nominal Support
--------------------------------------------------------------------------------

supp1gen :: forall n f s. (IsName n, Deciding1 (Nominal n) f) => (s -> Support n) -> f s -> Support n
supp1gen f = getSupported $ deciding1 (Proxy :: Proxy (Nominal n)) (Supported supp) (Supported f)

supply1gen :: forall n f s. (Enum n, IsName n, Deciding1 (Nominal n) f) => (s -> Supply n) -> f s -> Supply n
supply1gen f = getOp $ deciding1 (Proxy :: Proxy (Nominal n)) (Op supply) (Op f)

-- Could also be called NominalFunctor
class Permutable1 n f => Nominal1 n f where
  supp1 :: (s -> Support n) -> f s -> Support n
  default supp1 :: Deciding1 (Nominal n) f => (s -> Support n) -> f s -> Support n
  supp1 = supp1gen

  supply1 :: Enum n => (s -> Supply n) -> f s -> Supply n
  default supply1 :: (Enum n, Deciding1 (Nominal n) f) => (s -> Supply n) -> f s -> Supply n
  supply1 = supply1gen

instance IsName n => Nominal1 n []
instance IsName n => Nominal1 n Maybe
instance IsName n => Nominal1 n Proxy
instance Nominal n a => Nominal1 n ((,) a)
instance (Nominal n a, Nominal n b) => Nominal1 n ((,,) a b)
instance (Nominal n a, Nominal n b, Nominal n c) => Nominal1 n ((,,,) a b c)
instance Nominal n a => Nominal1 n (Either a)

-- (#) :: (Nominal n a, Nominal n b) => a -> b -> Bool
-- a # b = supp a `disjoint` supp b

--------------------------------------------------------------------------------
-- * Fresh
--------------------------------------------------------------------------------

class Fresh n a where
  refresh :: Supply n -> (a, Supply n)

fresh :: forall n s a. (Enum n, Nominal n s, Fresh n a) => Proxy n -> s -> a
fresh Proxy s = fst (refresh (supply s :: Supply n))

instance (Enum n, IsName n) => Fresh n (Name n) where
  refresh (Supply a) = (NameRepr a, Supply $ succ a)

instance Fresh n () where
  refresh = (,) ()

instance (Fresh n a, Fresh n b) => Fresh n (a, b) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> ((a,b),cs)

instance (Fresh n a, Fresh n b, Fresh n c) => Fresh n (a, b, c) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case refresh cs of
        (c,ds) -> ((a,b,c),ds)

instance (Fresh n a, Fresh n b, Fresh n c, Fresh n d) => Fresh n (a, b, c, d) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case refresh cs of
        (c,ds) -> case refresh ds of
          (d,es) -> ((a,b,c,d),es)

--------------------------------------------------------------------------------
-- * Lifted Fresh
--------------------------------------------------------------------------------

class Fresh1 n f where
  refresh1 :: (Supply n -> (a, Supply n)) -> Supply n -> (f a, Supply n)

instance Fresh n a => Fresh1 n ((,) a) where
  refresh1 f as = case refresh as of
    (a,bs) -> case f bs of
      (b,cs) -> ((a,b),cs)

instance (Fresh n a, Fresh n b) => Fresh1 n ((,,) a b) where
  refresh1 f as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case f cs of
         (c,ds) -> ((a,b,c),ds)

instance (Fresh n a, Fresh n b, Fresh n c) => Fresh1 n ((,,,) a b c) where
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
class (Nominal n a, Semigroup a) => NominalSemigroup n a where
instance IsName n => NominalSemigroup n (Set n)
instance IsName n => NominalSemigroup n (Permutation n)

instance (NominalSemigroup n a, NominalSemigroup n b) => NominalSemigroup n (a, b)
instance IsName n => NominalSemigroup n (Support n)

--------------------------------------------------------------------------------
-- * Nominal Monoids
--------------------------------------------------------------------------------

-- | perm is a unital group action
--
-- @
-- perm p mempty = mempty
-- supp mempty = mempty -- mempty has empty support
-- @
class (NominalSemigroup n a, Monoid a) => NominalMonoid n a
instance IsName n => NominalMonoid n (Permutation n)
instance IsName n => NominalMonoid n (Set n)
instance (NominalMonoid n a, NominalMonoid n b) => NominalMonoid n (a, b)

-- TODO: Nominal lattices, etc?

-- -}
--------------------------------------------------------------------------------
-- * GHC Generics Support
--------------------------------------------------------------------------------

class GPermutable n f where
  gtrans :: Name n -> Name n -> f a -> f a
  gperm :: Permutation n -> f a -> f a

instance Permutable n c => GPermutable n (K1 i c) where
  gtrans i j (K1 a) = K1 (trans i j a)
  gperm p (K1 a) = K1 (perm p a)

instance GPermutable n f => GPermutable n (M1 i c f) where
  gtrans i j (M1 a) = M1 (gtrans i j a)
  gperm p (M1 a) = M1 (gperm p a)

instance GPermutable n V1 where
  gtrans _ _ !v = case v of {}
  gperm _ !v = case v of {}

instance GPermutable n U1 where
  gtrans _ _ U1 = U1
  gperm _ U1 = U1

instance (GPermutable n f, GPermutable n g) => GPermutable n (f :*: g) where
  gtrans i j (a :*: b) = gtrans i j a :*: gtrans i j b
  gperm p (a :*: b) = gperm p a :*: gperm p b

instance (GPermutable n f, GPermutable n g) => GPermutable n (f :+: g) where
  gtrans i j (L1 a) = L1 (gtrans i j a)
  gtrans i j (R1 a) = R1 (gtrans i j a)
  gperm p (L1 a) = L1 (gperm p a)
  gperm p (R1 a) = R1 (gperm p a)

instance (Permutable1 n f, GPermutable n g) => GPermutable n (f :.: g) where
  gtrans i j (Comp1 a) = Comp1 (trans1 gtrans i j a)
  gperm p (Comp1 a) = Comp1 (perm1 gperm p a)

class GPermutable1 n f where
  gtrans1 :: (Name n -> Name n -> a -> b) -> Name n -> Name n -> f a -> f b
  gperm1 :: (Permutation n -> a -> b) -> Permutation n -> f a -> f b

instance Permutable n c => GPermutable1 n (K1 i c) where
  gtrans1 _ i j (K1 a) = K1 (trans i j a)
  gperm1 _ p (K1 a) = K1 (perm p a)

instance GPermutable1 n f => GPermutable1 n (M1 i c f) where
  gtrans1 f i j (M1 a) = M1 (gtrans1 f i j a)
  gperm1 f p (M1 a) = M1 (gperm1 f p a)

instance GPermutable1 n V1 where
  gtrans1 _ _ _ !v = case v of {}
  gperm1 _ _ !v = case v of {}

instance GPermutable1 n U1 where
  gtrans1 _ _ _ U1 = U1
  gperm1 _ _ U1 = U1

instance (GPermutable1 n f, GPermutable1 n g) => GPermutable1 n (f :*: g) where
  gtrans1 f i j (a :*: b) = gtrans1 f i j a :*: gtrans1 f i j b
  gperm1 f p (a :*: b) = gperm1 f p a :*: gperm1 f p b

instance (GPermutable1 n f, GPermutable1 n g) => GPermutable1 n (f :+: g) where
  gtrans1 f i j (L1 a) = L1 (gtrans1 f i j a)
  gtrans1 f i j (R1 a) = R1 (gtrans1 f i j a)
  gperm1 f p (L1 a) = L1 (gperm1 f p a)
  gperm1 f p (R1 a) = R1 (gperm1 f p a)

instance (Permutable1 n f, GPermutable1 n g) => GPermutable1 n (f :.: g) where
  gtrans1 f i j (Comp1 a) = Comp1 (trans1 (gtrans1 f) i j a)
  gperm1 f p (Comp1 a) = Comp1 (perm1 (gperm1 f) p a)

instance GPermutable1 n Par1 where
  gtrans1 f i j (Par1 a) = Par1 (f i j a)
  gperm1 f p (Par1 a) = Par1 (f p a)

instance Permutable1 n f => GPermutable1 n (Rec1 f) where
  gtrans1 f i j (Rec1 a) = Rec1 (trans1 f i j a)
  gperm1 f p (Rec1 a) = Rec1 (perm1 f p a)

--------------------------------------------------------------------------------
-- * Computing permutations from perm-sets
--------------------------------------------------------------------------------

newtype Binder n a = Binder { getBinder :: a -> a -> Maybe (Permutation n) }

instance Contravariant (Binder n) where
  contramap f (Binder g) = Binder $ \x y -> g (f x) (f y)

instance IsName n => Divisible (Binder n) where
  conquer = Binder $ \ _ _ -> Just mempty
  divide f (Binder g) (Binder h) = Binder $ \x y -> case f x of
    (b, c) -> case f y of
       (d, e) -> (<>) <$> g b d <*> h c e

instance IsName n => Decidable (Binder n) where
  lose f = Binder $ absurd . f
  choose f (Binder g) (Binder h) = Binder $ \x y -> case f x of
    Left b -> case f x of
      Left d -> g b d
      Right _ -> Nothing
    Right c -> case f y of
      Left _ -> Nothing
      Right e -> h c e

--------------------------------------------------------------------------------
-- * Bindings
--------------------------------------------------------------------------------

-- assumption: all variables in a binding are distinct
class Nominal n a => Binding n a where
  binding :: a -> a -> Maybe (Permutation n)
  default binding :: Deciding (Binding n) a => a -> a -> Maybe (Permutation n)
  binding a b = getBinder (deciding (Proxy :: Proxy (Binding n)) (Binder binding)) a b

  bv :: a -> Set n
  default bv :: Deciding (Binding n) a => a -> Set n
  bv = getOp $ deciding (Proxy :: Proxy (Binding n)) $ Op bv

instance IsName n => Binding n (Name n) where
  binding a b = Just (swap a b)
  bv = Set.singleton

instance IsName n => Binding n () where
  binding _ _ = Just mempty
  bv = mempty

instance IsName n => Binding n Void where
  binding = absurd
  bv = absurd

instance IsName n => Binding n Int where
  binding a b = mempty <$ guard (a == b)
  bv = mempty

instance IsName n => Binding n Bool where
  binding a b = mempty <$ guard (a == b)
  bv = mempty

instance IsName n => Binding n Char where
  binding a b = mempty <$ guard (a == b)
  bv = mempty

instance (Binding n a, Binding n b) => Binding n (a, b)
instance (Binding n a, Binding n b, Binding n c) => Binding n (a, b, c)
instance (Binding n a, Binding n b, Binding n c, Binding n d) => Binding n (a, b, c, d)
instance (Binding n a, Binding n b) => Binding n (Either a b)
instance Binding n a => Binding n (Maybe a)
instance Binding n a => Binding n [a]

--------------------------------------------------------------------------------
-- * Lifted Bindings
--------------------------------------------------------------------------------

class Nominal1 n f => Binding1 n f where
  binding1 :: (a -> a -> Maybe (Permutation n)) -> f a -> f a -> Maybe (Permutation n)
  default binding1 :: Deciding1 (Binding n) f => (a -> a -> Maybe (Permutation n)) -> f a -> f a -> Maybe (Permutation n)
  binding1 f a b = getBinder (deciding1 (Proxy :: Proxy (Binding n)) (Binder binding) (Binder f)) a b

  bv1 :: (a -> Set n) -> f a -> Set n
  default bv1 :: Deciding1 (Binding n) f => (a -> Set n) -> f a -> Set n
  bv1 f = getOp $ deciding1 (Proxy :: Proxy (Binding n)) (Op bv) (Op f)

instance Binding n a => Binding1 n (Either a)
instance Binding n a => Binding1 n ((,) a)
instance (Binding n a, Binding n b) => Binding1 n ((,,) a b)
instance (Binding n a, Binding n b, Binding n c) => Binding1 n ((,,,) a b c)
instance IsName n => Binding1 n []
instance IsName n => Binding1 n Maybe

-- things that would need [Permutation]:
-- Binding Set isn't really possible, it'd need to give back several possible matchings, using, say, [Permutation]
-- Binding Support is worse
-- Binding Permutatation -- takes permutations to permutations but would need to choose which one of each cycle of the same length was which
-- Binding1 Map
-- Binding1 Trie

--------------------------------------------------------------------------------
-- * Irrefutable Matches
--------------------------------------------------------------------------------

class (IsName n, Binding n a) => Irrefutable n a where
  match :: a -> a -> Permutation n

instance IsName n => Irrefutable n (Name n) where
  match = swap -- TODO: move this far enough upstream so that match _is_ swap?

instance IsName n => Irrefutable n Void where
  match = absurd

instance IsName n => Irrefutable n () where
  match _ _ = mempty

instance (Irrefutable n a, Irrefutable n b) => Irrefutable n (a, b) where
  match (a,b) (c,d) = match a c <> match b d

instance (Irrefutable n a, Irrefutable n b, Irrefutable n c) => Irrefutable n (a, b, c) where
  match (a,b,c) (d,e,f) = match a d <> match b e <> match c f

instance (Irrefutable n a, Irrefutable n b, Irrefutable n c, Irrefutable n d) => Irrefutable n (a, b, c, d) where
  match (a,b,c,d) (e,f,g,h) = match a e <> match b f <> match c g <> match d h

--------------------------------------------------------------------------------
-- * Lifted Irrefutable Matches
--------------------------------------------------------------------------------

class Binding1 n f => Irrefutable1 n f where
  match1 :: (a -> a -> Permutation n) -> f a -> f a -> Permutation n

instance (Irrefutable n a) => Irrefutable1 n ((,) a) where
  match1 f (a,b) (c,d) = match a c <> f b d

instance (Irrefutable n a, Irrefutable n b) => Irrefutable1 n ((,,) a b) where
  match1 g (a,b,c) (d,e,f) = match a d <> match b e <> g c f

instance (Irrefutable n a, Irrefutable n b, Irrefutable n c) => Irrefutable1 n ((,,,) a b c) where
  match1 i (a,b,c,d) (e,f,g,h) = match a e <> match b f <> match c g <> i d h

--------------------------------------------------------------------------------
-- * Basic Support
--------------------------------------------------------------------------------

class Nominal n a => Basic n a

instance IsName n => Basic n Void
instance IsName n => Basic n ()
instance IsName n => Basic n Bool
instance IsName n => Basic n Char
instance IsName n => Basic n Int
instance Basic n a => Basic n [a]
instance Basic n a => Basic n (Maybe a)
instance (Basic n a, Basic n b) => Basic n (Either a b)
instance (Basic n a, Basic n b) => Basic n (a, b)
instance (Basic n a, Basic n b, Basic n c) => Basic n (a, b, c)
instance (Basic n a, Basic n b, Basic n c, Basic n d) => Basic n (a, b, c, d)

--------------------------------------------------------------------------------
-- * Lifted Basic Support
--------------------------------------------------------------------------------

class Nominal1 n f => Basic1 n f

instance IsName n => Basic1 n []
instance IsName n => Basic1 n Maybe
instance Basic n a => Basic1 n (Either a)
instance Basic n a => Basic1 n ((,) a)
instance (Basic n a, Basic n b) => Basic1 n ((,,) a b)
instance (Basic n a, Basic n b, Basic n c) => Basic1 n ((,,,) a b c)