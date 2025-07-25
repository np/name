{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Name.Repr.Natural where

import Data.Discrimination.Grouping
import Numeric.Natural
import Control.Lens (Contravariant(..))
import Data.Coerce (coerce)
import Data.Name.Class (IsNameRepr)

newtype NatNameRepr = NatNameRepr Natural deriving (Eq,Enum,Ord)

instance Grouping NatNameRepr where
  grouping = contramap coerce (grouping :: Group Natural)
  {-# inlineable grouping #-}

instance Show NatNameRepr where
  showsPrec d (NatNameRepr n) = showsPrec d n
  {-# inlineable showsPrec #-}

instance IsNameRepr NatNameRepr where