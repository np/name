module Data.Name.Repr.Atom (AtomNameRepr) where

import Data.Discrimination.Grouping
import Data.Name.Class (IsNameRepr)
import Control.Lens (contramap)
import Numeric.Natural

data AtomNameRepr = AtomNameRepr { _atomBaseName :: String
                                 , _atomUniqueId :: Natural
                                 } deriving (Eq, Ord)

instance Grouping AtomNameRepr where
  grouping = contramap _atomUniqueId (grouping :: Group Natural)
  {-# inlineable grouping #-}

instance Show AtomNameRepr where
  showsPrec d (AtomNameRepr baseName uniqueId) =
    showString baseName . showChar '_' . showsPrec d uniqueId
  {-# inlineable showsPrec #-}

instance IsNameRepr AtomNameRepr where