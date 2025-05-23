module Data.Name.Internal.IsNameRepr where

import Data.Discrimination (Grouping)

-- TODO: Eq is a definite superclass, ideally Ord/Hashable/Show/Read should go through an Iso.
-- Meanwhile we have Ord/Show as superclass
class (Ord n, Show n, Grouping n) => IsNameRepr n where