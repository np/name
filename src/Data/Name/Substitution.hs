{-# Language EmptyCase #-}
{-# Language TypeOperators #-}
{-# Language DefaultSignatures #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language UndecidableInstances #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}

module Data.Name.Substitution
( Subst(..), substgen, substexp, GSubst
, Subst1(..), subst1gen, GSubst1
) where

import Control.Lens hiding (to, from)
import Data.Maybe
import Data.Name.Class
import Data.Name.Lattice
import Data.Name.Map as Map
import Data.Name.Permutation
import Data.Name.Set as Set
import Data.Name.Support
import Data.Name.Tie
import GHC.Generics
import Data.Name.Type (Name)

-- TODO: fuse the 'perm' call into 'subst'
-- TODO: use the 'Shared' trick from ermine or the pointer check from containers to increase term sharing.

substgen :: (Generic a, GSubst n e (Rep a)) => Map n e -> Permutation n -> a -> a
substgen m p = to . gsubst m p . from

class Nominal n e => Subst n e a where
  subst :: Map n e -> Permutation n -> a -> a
  default subst :: (Generic a, GSubst n e (Rep a)) => Map n e -> Permutation n -> a -> a
  subst = substgen

instance (Subst n e a, Subst n e b) => Subst n e (a, b)
instance (Subst n e a, Subst n e b) => Subst n e (Either a b)
instance Subst n e a => Subst n e [a]
instance Subst n e a => Subst n e (Maybe a)

subst1gen :: (Generic1 f, GSubst1 n e (Rep1 f)) => (Map n e -> Permutation n -> a -> a) -> Map n e -> Permutation n -> f a -> f a
subst1gen f m p = to1 . gsubst1 f m p . from1

class Nominal n e => Subst1 n e f where
  subst1 :: (Map n e -> Permutation n -> a -> a) -> Map n e -> Permutation n -> f a -> f a
  default subst1 ::  (Generic1 f, GSubst1 n e (Rep1 f)) => (Map n e -> Permutation n -> a -> a) -> Map n e -> Permutation n -> f a -> f a
  subst1 = subst1gen

class Nominal n e => GSubst n e f where
  gsubst :: Map n e -> Permutation n -> f a -> f a

instance Subst n e c => GSubst n e (K1 i c) where
  gsubst m p (K1 v) = K1 (subst m p v)

instance Nominal n e => GSubst n e V1 where
  gsubst _ _ v = v `seq` case v of {}

instance GSubst n e f => GSubst n e (M1 i c f) where
  gsubst m p (M1 v) = M1 (gsubst m p v)

instance Nominal n e => GSubst n e U1 where
  gsubst _ _ U1 = U1

instance (GSubst n e f, GSubst n e g) => GSubst n e (f :*: g) where
  gsubst m p (x :*: y) = gsubst m p x :*: gsubst m p y

instance (GSubst n e f, GSubst n e g) => GSubst n e (f :+: g) where
  gsubst m p (L1 x) = L1 (gsubst m p x)
  gsubst m p (R1 x) = R1 (gsubst m p x)

instance (Subst1 n e f, GSubst n e g) => GSubst n e (f :.: g) where
  gsubst m p (Comp1 fgx) = Comp1 $ subst1 gsubst m p fgx

class Nominal n e => GSubst1 n e f where
  gsubst1 :: (Map n e -> Permutation n -> a -> a) -> Map n e -> Permutation n -> f a -> f a

instance Nominal n e => GSubst1 n e V1 where
  gsubst1 _ _ _ v = v `seq` case v of {}

instance Nominal n e => GSubst1 n e U1 where
  gsubst1 _ _ _ U1 = U1

instance (GSubst1 n e f, GSubst1 n e g) => GSubst1 n e (f :*: g) where
  gsubst1 f m p (x :*: y) = gsubst1 f m p x :*: gsubst1 f m p y

instance (GSubst1 n e f, GSubst1 n e g) => GSubst1 n e (f :+: g) where
  gsubst1 f m p (L1 x) = L1 $ gsubst1 f m p x
  gsubst1 f m p (R1 x) = R1 $ gsubst1 f m p x

instance (Subst1 n e f, GSubst1 n e g) => GSubst1 n e (f :.: g) where
  gsubst1 f m p (Comp1 fgx) = Comp1 $ subst1 (gsubst1 f) m p fgx

instance Subst n e c => GSubst1 n e (K1 i c) where
  gsubst1 _ m p (K1 v) = K1 (subst m p v)

instance GSubst1 n e f => GSubst1 n e (M1 i c f) where
  gsubst1 f m p (M1 v) = M1 (gsubst1 f m p v)

instance Nominal n e => GSubst1 n e Par1 where
  gsubst1 f m p (Par1 a) = Par1 (f m p a)

instance Subst1 n e f => GSubst1 n e (Rec1 f) where
  gsubst1 f m p (Rec1 x) = Rec1 (subst1 f m p x)

substexp :: (Generic e, AsName n e, GSubst n e (Rep e)) => Map n e -> Permutation n -> e -> e
substexp m p t = case t^?_Name of
  Just (perm p -> v) -> fromMaybe (review _Name v) $ Map.lookup v m
  Nothing -> substgen m p t

instance {-# overlappable #-} 
  ( AsName n e
  , Generic e
  , GSubst n e (Rep e)
  , Nominal n e -- why can't this find it via the superclass of GSubst n e (Rep e)?
  ) => Subst n e e where
  subst = substexp

instance {-# overlapping #-} IsName n => Subst n (Name n) (Name n) where
  subst m p (perm p -> a) = fromMaybe a $ Map.lookup a m

instance (Num n, Subst n e a, Binding n a, Subst n e b, Nominal n b) => Subst n e (Tie n a b) where
  subst m p (Tie a b)
    | p' <- fst $ Set.foldr step (p, supply (m, p, a, b) :: Supply n) $ bv a /\ perm (inv p) (coarsest (supp m)) -- (m,p,a,b) is conservative but cheap
    = Tie (subst m p' a) (subst m p' b)
    where step u (x, vs) = case refresh vs of
            (v,vs') -> (swap u v <> x, vs')