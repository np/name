{-# language TypeFamilies #-}
{-# language FlexibleContexts #-}
{-# language RankNTypes #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Internal.Perm where

import Control.Lens
import Control.Monad
import Data.Maybe
import Data.Name.Internal.IsName
import Data.Name.Internal.Trie
import Prelude hiding (elem, lookup)
import Data.Name.Type (Name(..))

{- REMARK on why Ord is commented out.

The `Ord` instance on `Perm` leaks the `Ord` on `Name` since
`cmp (swap a b) (swap a c)` equals `cmp (_nameRepr b) (_nameRepr c)`.

-}

newtype Perm n = Perm { getPerm :: Trie n n }
  deriving (Eq,{-Ord,-}Show)

perm' :: IsName n => Perm n -> Name n -> Name n
perm' (Perm t) a = maybe a NameRepr $ lookup a t

inv' :: IsName n => Perm n -> Perm n
inv' (Perm x) = Perm $ ifoldr (\(NameRepr a) b -> insert (NameRepr b) a) Empty x

square' :: IsName n => Perm n -> Perm n
square' (Perm t) = Perm $ ifilterMap go t where
  go (NameRepr i) j = mfilter (i/=) $ lookup (NameRepr j) t -- check this

sup' :: Perm n -> Maybe (Name n)
sup' (Perm t) = sup t

instance IsName n => Semigroup (Perm n) where
  --  x       y        z
  --  ----    ----     ------
  --  0->1             0 -> 2
  --  1->0    1->2     1 -> 0
  --          2->1     2 -> 1
  Perm x <> yt@(Perm y) = Perm $ ifilterMap f $ union (_nameRepr . perm' yt . NameRepr <$> x) y where
    f (NameRepr i) = mfilter (i/=) . pure

elem :: IsName n => Name n -> Lens' (Perm n) n
elem i f (Perm s) = Perm <$> at i (non (_nameRepr i) f) s

instance IsName n => Monoid (Perm n) where
  mempty = Perm Empty
