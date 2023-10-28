---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Map
( Map
, union
, intersectionWith
, intersection
, diff
, (\\)
, lookup
, delete
, insert
, singleton
, empty
) where

import Prelude hiding (lookup)
import Data.Name.Internal.Map
