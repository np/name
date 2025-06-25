module Data.Name.Repr.PrefixUnique (PrefixUniqueNameRepr(..)) where

import Data.Discrimination.Grouping
import Data.Name.Class (IsNameRepr)
import Control.Lens (contramap)
import Data.Unique (Unique, hashUnique)

data PrefixUniqueNameRepr = PrefixUniqueNameRepr { _punrPrefix :: !String
                                                 , _punrUnique :: !Unique
                                                 } deriving (Eq, Ord)

instance Grouping PrefixUniqueNameRepr where
  grouping = error "contramap _punrUnique (grouping :: Group Unique)"
  {-# inlineable grouping #-}

instance Show PrefixUniqueNameRepr where
  showsPrec d (PrefixUniqueNameRepr prefix unique) =
    showString prefix . showChar '_' . showsPrec d (hashUnique unique)
  {-# inlineable showsPrec #-}

instance IsNameRepr PrefixUniqueNameRepr where