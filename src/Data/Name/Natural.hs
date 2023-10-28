{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Name.Natural where

import Data.Discrimination.Grouping
import Numeric.Natural
import Control.Lens (Contravariant(..))
import Data.Coerce (coerce)
import Data.Name.Class (IsName)

newtype NatNameRepr = NatNameRepr Natural deriving (Eq,Num,Ord)

instance Grouping NatNameRepr where
  grouping = contramap coerce (grouping :: Group Natural)
  {-# inlineable grouping #-}

instance Show NatNameRepr where
  showsPrec d (NatNameRepr n) = showsPrec d n
  {-# inlineable showsPrec #-}

instance IsName NatNameRepr where