{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language PatternSynonyms #-}
{-# language LambdaCase #-}
{-# language ConstraintKinds #-}
{-# language DefaultSignatures #-}
{-# language MultiParamTypeClasses #-}
{-# language GADTs #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Set where

import Control.Lens
import Control.Monad (guard)
import Data.Functor.Classes
import Data.Maybe (isJust)
import Data.Name.Lattice
import qualified Data.Name.Internal.Trie as Trie
import Data.Name.Internal.IsName (IsName)
import Data.Name.Internal.Trie (Trie)
import GHC.Exts (IsList(..))
import Unsafe.Coerce
import Data.Name.Type (Name (..))

data Set n where
  Set :: Trie n a -> Set n

foldr :: (Name n -> r -> r) -> r -> Set n -> r
foldr f z (Set t) = ifoldr (\i _ r -> f i r) z t
{-# inline foldr #-}

instance Eq n => Eq (Set n) where
  Set x == Set y = liftEq (\_ _ -> True) x y

instance Ord n => Ord (Set n) where
  Set x `compare` Set y = liftCompare (\_ _ -> EQ) x y -- what?

instance Show n => Show (Set n) where
  showsPrec d (Set xs) = showsPrec d $ _nameRepr <$> ifoldr (\i _ r -> i:r) [] xs

instance IsName n => IsList (Set n) where
  type Item (Set n) = Name n
  fromList = Prelude.foldr insert mempty
  toList (Set xs) = ifoldr (\i _ r -> i : r) [] xs
  
instance IsName n => PartialOrder (Set n) where
  Set a ⊆ Set b = Trie.isSubtrieOfBy (\_ _ -> True) a b

instance IsName n => Semigroup (Set n) where
  Set m <> Set n = Set (Trie.union m (unsafeCoerce n)) -- evil

instance IsName n => Monoid (Set n) where
  mempty = Set Empty

instance IsName n => Join (Set n)

instance IsName n => BoundedJoin (Set n)

instance IsName n => Meet (Set n) where
  Set m ∧ Set n = Set (Trie.intersection m n)

instance IsName n => DistributiveLattice (Set n)

instance IsName n => GBA (Set n) where
  Set m \\ Set n = Set (Trie.diff m n)

instance IsName n => AsEmpty (Set n) where
  _Empty = prism (const (Set Empty)) $ \case
    Set Empty -> Right ()
    x -> Left x

type instance Index (Set n) = Name n

instance IsName n => Contains (Set n) where
  contains a f (Set e) = Set <$> at a (fmap guard' . f . isJust) e where
    guard' :: Bool -> Maybe a
    guard' b = undefined <$ guard b

class Contains a => SetLike a where
  insert :: Index a -> a -> a
  insert a = contains a .~ True
  {-# inline insert #-}

  delete :: Index a -> a -> a
  delete a = contains a .~ False
  {-# inline delete #-}

  member :: Index a -> a -> Bool
  member = view . contains
  {-# inline member #-}

  singleton :: Index a -> a
  default singleton :: BoundedJoin a => Index a -> a
  singleton a = insert a bottom
  {-# inline singleton #-}

infixr 6 +>

(+>) :: SetLike a => Index a -> a -> a
(+>) = insert

instance IsName n => SetLike (Set n) where
  insert a (Set t) = Set (Trie.insert a undefined t)
  delete a (Set t) = Set (Trie.delete a t)
  member a (Set t) = Trie.member a t
  singleton a      = Set (Trie.singleton a ())

disjoint :: IsName n => Set n -> Set n -> Bool
disjoint (Set a) (Set b) = Trie.disjoint a b
