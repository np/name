
{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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

module Data.Name.Internal.Map where

import Control.Lens hiding ((#))
import Data.Functor.Compose ( Compose(Compose, getCompose) )
import Data.Name.Class
import qualified Data.Name.Internal.Trie as Trie
import Data.Name.Internal.Trie (Trie(..))
import Data.Name.Support ( Support(..) )
import Data.Functor (void)
import Data.Name.Type (Name)

-- maps from atoms to values, contains a memoized approximate support
data Map n a = Map !(Support n) !(Trie n a)

-- equivariant
union :: NominalSemigroup n a => Map n a -> Map n a -> Map n a
union (Map s0a t0a) (Map s0b t0b) = Map (s0a <> s0b) (t0a <> t0b)

instance NominalSemigroup n a => Semigroup (Map n a) where
  (<>) = union

empty :: IsNameRepr n => Map n a
empty = Map mempty Empty
{-# INLINE empty #-}

instance NominalSemigroup n a => Monoid (Map n a) where
  mempty = empty

instance NominalSemigroup n a => NominalSemigroup n (Map n a)

instance NominalSemigroup n a => NominalMonoid n (Map n a)

-- requires a equivariant morphism, if so, equivariant
intersectionWith :: IsNameRepr n => (a -> b -> c) -> Map n a -> Map n b -> Map n c
intersectionWith f (Map s0 t0) (Map s1 t1) = case Trie.intersectionWith f t0 t1 of
  Empty -> empty
  t     -> Map (s0 <> s1) t

-- equivariant
intersection :: IsNameRepr n => Map n a -> Map n a -> Map n a
intersection (Map s0 t0) (Map _ t1) = case Trie.intersection t0 t1 of
  Empty -> empty
  t     -> Map s0 t

-- equivariant
diff :: Nominal n s => Map n a -> s -> Map n a
diff (Map s0 t0) (supp -> Supp t1) = case Trie.diff t0 t1 of
  Empty -> empty
  t -> Map s0 t

-- equivariant
(\\) :: Nominal n s => Map n a -> s -> Map n a
(\\) = diff

-- equivariant
lookup :: IsNameRepr n => Name n -> Map n a -> Maybe a
lookup i (Map _ t) = Trie.lookup i t

-- equivariant
delete :: IsNameRepr n => Name n -> Map n a -> Map n a
delete i (Map s0 t0) = case Trie.delete i t0 of
  Empty -> empty
  t -> Map s0 t

-- equivariant
insert :: (IsNameRepr n, Nominal n a) => Name n -> a -> Map n a -> Map n a
insert v a (Map s t) = Map (supp v <> supp a <> s) $ Trie.insert v a t

-- equivariant
singleton :: (IsNameRepr n, Nominal n a) => Name n -> a -> Map n a
singleton v a = Map (supp v <> supp a) (Trie.singleton v a)

type instance Index (Map n a) = Name n
type instance IxValue (Map n a) = a
instance Nominal n a => Ixed (Map n a)
instance Nominal n a => At (Map n a) where
  at a0 f0 (Map s0 t0) = tweak <$> getCompose (at a0 (Compose . fmap diag . f0) t0) where
    diag a = (a,a)
    tweak (_, Empty)  = empty
    tweak (Just a,t)  = Map (supp a0 <> supp a <> s0) t
    tweak (Nothing,t) = Map s0 t

instance IsNameRepr n => AsEmpty (Map n a) where
  _Empty = prism (const empty) $ \case
    Map _ Empty -> Right ()
    t           -> Left t

-- equivariant, clean up the cached support
trim :: Nominal n a => Map n a -> Map n a
trim (Map _ t0) = Map (Supp (void t0) <> foldMap supp t0) t0

instance IsNameRepr n => Permutable1 n (Map n) where
  perm1 f p (Map s t) = Map (perm p s) (perm1 f p t)
  trans1 f i j (Map s t) = Map (trans i j s) (trans1 f i j t)

instance Permutable n a => Permutable n (Map n a) where
  perm p (Map s t) = Map (perm p s) (perm p t)
  trans i j (Map s t) = Map (trans i j s) (trans i j t)

instance Permutable n a => Nominal n (Map n a) where
  a # (Map s _) = a # s
  supp (Map s _) = s
  equiv (Map s _) = equiv s
  supply (Map s _) = supply s

