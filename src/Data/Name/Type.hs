{-# LANGUAGE ScopedTypeVariables #-}
---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Type
( Name(..)
) where
import Data.Discrimination (Grouping, Group)
import Data.Discrimination.Grouping (Grouping(..))
import Control.Lens (Contravariant(..))
import Data.Coerce (coerce)

-- By design, a `Name` is meant to support the minimum amount of instances.
-- It has `Eq` and `Grouping`.
-- It has `Show` for debugging.
-- Its representation might have `Ord`, `Hashable`, `Num`...
newtype Name n = NameRepr { _nameRepr :: n }
  deriving (Eq, Show)

instance Grouping n => Grouping (Name n) where
  grouping = contramap coerce (grouping :: Group n)
  {-# inlineable grouping #-}