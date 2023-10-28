{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language DeriveGeneric #-}
{-# language DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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

module Data.Name.Tie where

import GHC.Generics
import Data.Name.Category
import qualified Data.Name.Internal.Trie as Trie
import Data.Name.Class
import Data.Name.Lattice
import Data.Name.Set
import Data.Name.Support
import Data.Name.Permutation (Permutation)
import Data.Data (Proxy(..))
import Data.Name.Type (Name)

data Tie n a b = Tie a b
  deriving (Generic, Generic1, Show, Functor, Foldable, Traversable)

instance (Eq a, Binding n a, Eq b, Nominal n b) => Eq (Tie n a b) where
  Tie a as == Tie b bs
    | a == b = as == bs
    | otherwise = case (binding a b :: Maybe (Permutation n)) of
      Nothing -> False
      Just p  -> sep bs ((bv a :: Set n) \\ bv b) && as == perm p bs

sep :: Nominal n a => a -> Set n -> Bool
sep (supp -> Supp s) (Set t) = Trie.disjoint s t
{-# inline sep #-}

instance (Permutable n a, Permutable n b) => Permutable n (Tie n a b) where
  trans i j (Tie a b) = Tie (trans i j a) (trans i j b)
  {-# inline trans #-}
  perm s (Tie a b) = Tie (perm s a) (perm s b)
  {-# inline perm #-}

instance Permutable n a => Permutable1 n (Tie n a) where
  perm1 f s (Tie a b) = Tie (perm s a) (f s b)
  {-# inline perm1 #-}
  trans1 f i j (Tie a b) = Tie (trans i j a) (f i j b)
  {-# inline trans1 #-}

instance (Binding n a, Nominal n b) => Nominal n (Tie n a b) where
  a # Tie b x = member a (bv b) || a # x
  {-# inline (#) #-}
  supp (Tie a b) = supp b `sans` bv a
  {-# inline supp #-}

instance Binding n a => Nominal1 n (Tie n a) where
  supp1 f (Tie a b) = f b `sans` bv a

unziptie :: forall n k a x y. N n k => k (Tie n a (x, y)) (Tie n a x, Tie n a y)
unziptie = nom (mempty :: Support n) $ \(Tie a (x,y)) -> (Tie a x, Tie a y)

ziptie :: forall n k a x y. (NI n k, Irrefutable n a, Permutable n y) => k (Tie n a x, Tie n a y) (Tie n a (x, y))
ziptie = niso (mempty :: Support n) f unziptie where
  f (Tie a as, Tie b bs) = Tie a (as, perm (match a b :: Permutation n) bs)

coziptie :: forall n k a x y. NI n k => k (Either (Tie n a x) (Tie n a y)) (Tie n a (Either x y))
coziptie = niso (mempty :: Support n) f g where
  f (Left (Tie a as)) = Tie a (Left as)
  f (Right (Tie a as)) = Tie a (Right as)
  g (Tie a (Left as)) = Left (Tie a as)
  g (Tie a (Right bs)) = Right (Tie a bs)

delta :: forall n k a b c. NI n k => k (Tie n a (Tie n b c)) (Tie n b (Tie n a c))
delta = niso (mempty :: Support n) (\(Tie a (Tie b c)) -> Tie b (Tie a c)) (\(Tie a (Tie b c)) -> Tie b (Tie a c))

kappa :: forall n k a b. (N n k, Num n, Nominal n a, Fresh n b) => k a (Tie n b a)
kappa = nom (mempty :: Support n) $ \x -> Tie (fresh (Proxy :: Proxy n) x) x

-- side condition: a # b
data Untie n a b = Untie a b deriving (Eq, Show, Generic, Generic1)

instance (Permutable n a, Permutable n b) => Permutable n (Untie n a b)
instance Permutable n a => Permutable1 n (Untie n a)
instance (Nominal n a, Binding n b) => Nominal n (Untie n a b)
instance Nominal n a => Nominal1 n (Untie n a)
instance (Binding n a, Binding n b) => Binding n (Untie n a b)
instance Binding n a => Binding1 n (Untie n a)

instance (Irrefutable n a, Irrefutable n b) => Irrefutable n (Untie n a b) where
  match (Untie a b) (Untie c d) = match a c <> match b d

instance Irrefutable n a => Irrefutable1 n (Untie n a) where
  match1 f  (Untie a b) (Untie c d) = match a c <> f b d

pi1 :: forall n k a b. N n k => k (Untie n a b) a
pi1 = nom (mempty :: Support n) $ \ (Untie a _) -> a

pi2 :: forall n k a b. N n k => k (Untie n a b) b
pi2 = nom (mempty :: Support n) $ \ (Untie _ b) -> b

-- this requires a 'fresh', what subset of irrefutable definitions match here?

unit :: forall n k a b. (Num n, N n k, Nominal n a, Fresh n b) => k a (Tie n b (Untie n a b))
unit = nom (mempty :: Support n) $ \ a -> let b = fresh (Proxy :: Proxy n) a in Tie b (Untie a b)

counit :: forall n k a b. (N n k, Permutable n a, Irrefutable n b) => k (Untie n (Tie n b a) b) a
counit = nom (mempty :: Support n) $ \(Untie (Tie d a) c) -> perm (match c d :: Permutation n) a

leftAdjunct :: forall n k a b c. (Num n, N n k, Nominal n a, Fresh n c) => k (Untie n a c) b -> k a (Tie n c b)
leftAdjunct = nar (Proxy :: Proxy n) $ \f y ->
   let a = fresh (Proxy :: Proxy n) y
   in Tie a (f (Untie y a))

rightAdjunct :: forall n k a b c. (N n k, Permutable n b, Irrefutable n c) => k a (Tie n c b) -> k (Untie n a c) b
rightAdjunct = nar (Proxy :: Proxy n) $ \f (Untie y c) -> case f y of
  Tie d x -> perm (match c d :: Permutation n) x

paired :: forall n k a. (NI n k, Permutable n a) => k (Untie n (Tie n (Name n) a) (Name n)) (Name n, a)
paired = niso (mempty :: Support n) f g where
  f (Untie (Tie a x) a') = (a', trans a' a x)
  g (a, x) = Untie (Tie a x) a