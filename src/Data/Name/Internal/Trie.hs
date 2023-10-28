{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -funbox-strict-fields -fno-warn-orphans -fno-warn-type-defaults -O2 #-}
#ifdef ST_HACK
{-# OPTIONS_GHC -fno-full-laziness #-}
#endif

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Internal.Trie
{-
  ( Trie
  , singleton
  , empty
  , insert
  , lookup
  , delete
  , member
  , fromList
  , sup
  , unionWith
  , union
  , intersectionWith
  , intersection
  , diff
  ) -} where

import Control.Arrow ((***))
import Control.Lens
    ( prism,
      FoldableWithIndex(ifoldMap),
      FunctorWithIndex(..),
      TraversableWithIndex(..),
      At(..),
      Index,
      IxValue,
      Ixed,
      AsEmpty(..) )
import Data.Coerce ( coerce )
import Data.Functor.Bind
import Data.Functor.Classes ( Eq1, Ord1, Show1 )
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Monoid
import Data.Name.Internal.IsName (IsName)
import GHC.Types
import Prelude hiding (lookup, length, foldr)
import Data.Name.Type (Name (..))

newtype Trie n v = Trie { runTrie :: Map n v } deriving
  ( Eq, Ord, Show
  , Functor, Foldable, Traversable
  , Eq1, Ord1, Show1
  , Apply, Bind
  )

sup :: Trie n a -> Maybe (Name n)
sup = fmap (NameRepr . fst . fst) . Map.maxViewWithKey . runTrie
{-# inlineable sup #-}

instance FunctorWithIndex (Name n) (Trie n) where
  imap f (Trie m) = Trie (imap (coerce f) m)
  {-# inlineable imap #-}

instance FoldableWithIndex (Name n) (Trie n) where
  ifoldMap f (Trie m) = ifoldMap (coerce f) m
  {-# inlineable ifoldMap #-}

instance TraversableWithIndex (Name n) (Trie n) where
  itraverse f (Trie m) = Trie <$> itraverse (coerce f) m
  {-# inlineable itraverse #-}

insert :: IsName n => Name n -> v -> Trie n v -> Trie n v
insert (NameRepr a) v (Trie m) = Trie (Map.insert a v m)
{-# inlineable insert #-}

instance (IsName n, Semigroup a) => Semigroup (Trie n a) where
  Trie a <> Trie b = Trie (Map.unionWith (<>) a b)
  {-# inlineable (<>) #-}

instance (IsName n, Semigroup a) => Monoid (Trie n a) where
  mempty = Trie mempty
  {-# inlineable mempty #-}

unionWith :: IsName n => (a -> a -> a) -> Trie n a -> Trie n a -> Trie n a
unionWith f (Trie a) (Trie b) = Trie $ Map.unionWith f a b
{-# inlineable unionWith #-}

unionWithKey :: IsName n => (Name n -> a -> a -> a) -> Trie n a -> Trie n a -> Trie n a
unionWithKey f (Trie a) (Trie b) = Trie $ Map.unionWithKey (coerce f) a b
{-# inlineable unionWithKey #-}

union :: IsName n => Trie n a -> Trie n a -> Trie n a
union (Trie a) (Trie b) = Trie (Map.union a b)
{-# inlineable union #-}

intersection :: IsName n => Trie n a -> Trie n b -> Trie n a
intersection (Trie a) (Trie b) = Trie (Map.intersection a b)
{-# inlineable intersection #-}

-- segfaults
intersectionWith :: IsName n => (a -> b -> c) -> Trie n a -> Trie n b -> Trie n c
intersectionWith f (Trie a) (Trie b) = Trie $ Map.intersectionWith f a b
{-# inlineable intersectionWith #-}

intersectionWithKey :: IsName n => (Name n -> a -> b -> c) -> Trie n a -> Trie n b -> Trie n c
intersectionWithKey f (Trie a) (Trie b) = Trie $ Map.intersectionWithKey (coerce f) a b
{-# inlineable intersectionWithKey #-}

filterMap :: (a -> Maybe b) -> Trie n a -> Trie n b
filterMap f (Trie m) = Trie (Map.mapMaybe f m)
{-# inlineable filterMap #-}

ifilterMap :: (Name n -> a -> Maybe b) -> Trie n a -> Trie n b
ifilterMap f (Trie m) = Trie (Map.mapMaybeWithKey (f . NameRepr) m)
{-# inlineable ifilterMap #-}

filter :: (a -> Bool) -> Trie n a -> Trie n a
filter f (Trie m) = Trie (Map.filter f m)
{-# inlineable filter #-}

ifilter :: (Name n -> a -> Bool) -> Trie n a -> Trie n a
ifilter f (Trie m) = Trie (Map.filterWithKey (f . NameRepr) m)
{-# inlineable ifilter #-}

partition :: (a -> Bool) -> Trie n a -> (Trie n a, Trie n a)
partition f (Trie m) = (Trie *** Trie) $ Map.partition f m
{-# inlineable partition #-}

ipartition :: (Name n -> a -> Bool) -> Trie n a -> (Trie n a, Trie n a)
ipartition f (Trie m) = (Trie *** Trie) $ Map.partitionWithKey (f . NameRepr) m
{-# inlineable ipartition #-}

diff :: IsName n => Trie n a -> Trie n b -> Trie n a
diff (Trie m) (Trie n) = Trie (Map.difference m n)
{-# inlineable diff #-}

delete :: IsName n => Name n -> Trie n v -> Trie n v
delete (NameRepr !k) (Trie m) = Trie (Map.delete k m)
{-# inlineable delete #-}

(!) :: IsName n => Trie n v -> Name n -> v
(!) (Trie m) (NameRepr a) = m Map.! a
{-# inlineable (!) #-}

lookup :: IsName n => Name n -> Trie n v -> Maybe v
lookup (NameRepr a) (Trie m) = Map.lookup a m
{-# inlineable lookup #-}

member :: IsName n => Name n -> Trie n v -> Bool
member (NameRepr a) (Trie m) = Map.member a m
{-# inlineable member #-}

-- | Build a singleton Trie
singleton :: Name n -> v -> Trie n v
singleton (NameRepr a) v = Trie (Map.singleton a v)
{-# inlineable singleton #-}

fromList :: IsName n => [(Name n,v)] -> Trie n v
fromList = Trie . Map.fromList . coerce
{-# inlineable fromList #-}

fromDistinctAscList :: [(Name n,v)] -> Trie n v
fromDistinctAscList = Trie . Map.fromDistinctAscList . coerce
{-# inlineable fromDistinctAscList #-}

empty :: Trie n a
empty = Trie Map.empty
{-# inlineable empty #-}

type instance Index (Trie n a) = Name n
type instance IxValue (Trie n a) = a
instance IsName n => Ixed (Trie n a)
instance IsName n => At (Trie n a) where
  at (NameRepr i) f (Trie m) = Trie <$> at i f m
  {-# inline at #-}

instance IsName n => AsEmpty (Trie n a) where
  _Empty = prism (const (Trie mempty)) $ \m -> if null m then Right () else Left m
  {-# inline _Empty #-}

disjoint :: IsName n => Trie n a -> Trie n b -> Bool
disjoint m n = null (intersection m n)
{-# inlineable disjoint #-}

imerge
  :: IsName n
  => (n -> a -> b -> Maybe c)
  -> (Trie n a -> Trie n c)
  -> (Trie n b -> Trie n c)
  -> Trie n a -> Trie n b -> Trie n c
imerge f g h (Trie m) (Trie n) = Trie (Map.mergeWithKey f (coerce g) (coerce h) m n)
{-# inlineable imerge #-}

isSubtrieOfBy :: IsName n => (a -> b -> Bool) -> Trie n a -> Trie n b -> Bool
isSubtrieOfBy f (Trie a) (Trie b) = Map.isSubmapOfBy f a b
{-# inlineable isSubtrieOfBy #-}

isSubtrieOf :: (IsName n, Eq a) => Trie n a -> Trie n a -> Bool
isSubtrieOf (Trie a) (Trie b) = Map.isSubmapOf a b
{-# inline isSubtrieOf #-}
