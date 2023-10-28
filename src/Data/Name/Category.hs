{-# language ConstraintKinds #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language TypeApplications #-}
{-# language DefaultSignatures #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language DeriveFunctor #-}
{-# language DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Category where

import Control.Applicative (Applicative(..), Alternative(..))
import qualified Control.Arrow as Arrow
import Control.Category
import Control.Monad (guard)
import GHC.Exts
import GHC.Generics
import Data.Kind
import Data.Void
import Data.Name.Class
import Data.Name.Support
import qualified Prelude
import Prelude
  ( Either(..)
  , Eq(..), Ord(..), Show(..), Read(..), Maybe(..), Bool(..), Bounded(..), Enum(..)
  , ($)
  , Functor(..), (<$>)
  , Foldable(foldMap)
  , Monoid(..), Semigroup(..)
  )
import Data.Name.Type (Name)

type (+) = Either

data Nom n a b = Nom (Support n) (a -> b)

newtype Op k a b = Op { getOp :: k b a }
  deriving (Eq,Ord,Show,Read,Generic)

data Core k a b = Core { fwd :: k a b, bwd :: k b a }
  deriving (Eq,Ord,Show,Read,Generic)

invCore :: Core k a b -> Core k b a
invCore (Core f g) = Core g f

instance IsName n => Category (Nom n) where
  id = Nom mempty id
  {-# inline id #-}
  Nom s f . Nom t g = Nom (s<>t) (f.g)
  {-# inline (.) #-}

instance Category k => Category (Op k) where
  id = Op id
  {-# inline id #-}
  Op f . Op g = Op (g . f)
  {-# inline (.) #-}

instance Category k => Category (Core k) where
  id = Core id id
  {-# inline id #-}
  Core f g . Core h i = Core (f . h) (i . g)
  {-# inline (.) #-}

instance (Permutable n a, Permutable n b) => Permutable n (Nom n a b) where
  trans i j (Nom s f) = Nom (trans i j s) (trans i j f)
  perm p (Nom s f) = Nom (perm p s) (perm p f)

instance (Permutable n a, Permutable n b) => Nominal n (Nom n a b) where
  a # Nom s _ = a # s
  supp (Nom s _) = s
  supply (Nom s _) = supply s
  equiv (Nom s _) = equiv s

instance Permutable n (k b a) => Permutable n (Op (k :: * -> * -> *) a b)
instance Nominal n (k b a) => Nominal n (Op (k :: * -> * -> *) a b)

instance (Permutable n (k a b), Permutable n (k b a)) => Permutable n (Core k a b)
instance (Nominal n (k a b), Nominal n (k b a)) => Nominal n (Core k a b)

sepNom :: IsName n => Name n -> Nom n a b -> Bool
sepNom a (Nom s _) = a # s

suppNom :: Nom n a b -> Support n
suppNom (Nom s _) = s

runNom :: Nom n a b -> a -> b
runNom (Nom _ f) = f

class Category k => MonoidalP k where
  (***)   :: k a b -> k c d -> k (a,c) (b,d)
  first   :: k a b -> k (a,c) (b,c)
  second  :: k c d -> k (a,c) (a,d)
  swapP   :: k (a,b) (b,a)
  lassocP :: k (a,(b,c)) ((a,b),c)
  rassocP :: k ((a,b),c) (a,(b,c))
  lunit   :: k a ((),a)
  lcounit :: k ((),a) a
  runit   :: k a (a,())
  rcounit :: k (a,()) a

instance MonoidalP (->) where
  (***) f g (a,c) = (f a, g c)
  {-# inline (***) #-}
  first f (a, b) = (f a, b)
  {-# inline first #-}
  second g (a, b) = (a, g b)
  {-# inline second #-}
  swapP (a,b) = (b,a)
  {-# inline swapP #-}
  lassocP (a,(b,c)) = ((a,b),c)
  {-# inline lassocP #-}
  rassocP ((a,b),c) = (a,(b,c))
  {-# inline rassocP #-}
  lunit a = ((),a)
  {-# inline lunit #-}
  lcounit = Prelude.snd
  {-# inline lcounit #-}
  runit a = (a,())
  {-# inline runit #-}
  rcounit = Prelude.fst
  {-# inline rcounit #-}

instance IsName n => MonoidalP (Nom n) where
  Nom s f *** Nom t g = Nom (s <> t) (f *** g)
  {-# inline (***) #-}
  first (Nom s f) = Nom s (first f)
  {-# inline first #-}
  second (Nom s f) = Nom s (second f)
  {-# inline second #-}
  swapP :: IsName n => Nom n (a, b) (b, a)
  swapP = nom (mempty :: Support n) swapP
  {-# inline swapP #-}
  lassocP = nom (mempty :: Support n) lassocP
  {-# inline lassocP #-}
  rassocP = nom (mempty :: Support n) rassocP
  {-# inline rassocP #-}
  lunit = nom (mempty :: Support n) lunit
  {-# inline lunit #-}
  lcounit = nom (mempty :: Support n) lcounit
  {-# inline lcounit #-}
  runit = nom (mempty :: Support n) runit
  {-# inline runit #-}
  rcounit = nom (mempty :: Support n) rcounit
  {-# inline rcounit #-}

instance MonoidalP k => MonoidalP (Op k) where
  Op f *** Op g = Op (f *** g)
  {-# inline (***) #-}
  first (Op f) = Op (first f)
  {-# inline first #-}
  second (Op g) = Op (second g)
  {-# inline second #-}
  swapP = Op swapP
  {-# inline swapP #-}
  lassocP = Op rassocP
  {-# inline lassocP #-}
  rassocP = Op lassocP
  {-# inline rassocP #-}
  lunit = Op lcounit
  {-# inline lunit #-}
  runit = Op rcounit
  {-# inline runit #-}
  lcounit = Op lunit
  {-# inline lcounit #-}
  rcounit = Op runit
  {-# inline rcounit #-}

instance MonoidalP k => MonoidalP (Core k) where
  Core f g *** Core h i = Core (f *** h) (g *** i)
  {-# inline (***) #-}
  first (Core f g) = Core (first f) (first g)
  {-# inline first #-}
  second (Core f g) = Core (second f) (second g)
  {-# inline second #-}
  swapP = Core swapP swapP
  {-# inline swapP #-}
  lassocP = Core lassocP rassocP
  {-# inline lassocP #-}
  rassocP = Core rassocP lassocP
  {-# inline rassocP #-}
  lunit = Core lunit lcounit
  {-# inline lunit #-}
  runit = Core runit rcounit
  {-# inline runit #-}
  lcounit = Core lcounit lunit
  {-# inline lcounit #-}
  rcounit = Core rcounit runit
  {-# inline rcounit #-}

class MonoidalP k => Cartesian k where
  exl :: k (a,b) a
  exr :: k (a,b) b
  dup :: k a (a,a)
  it  :: k a ()

(&&&) :: Cartesian k => k a b -> k a c -> k a (b,c)
f &&& g = (f *** g) . dup
{-# inline (&&&) #-}

instance Cartesian (->) where
  exl = Prelude.fst
  {-# inline exl #-}
  exr = Prelude.snd
  {-# inline exr #-}
  dup a = (a,a)
  {-# inline dup #-}
  it _ = ()
  {-# inline it #-}

instance IsName n => Cartesian (Nom n) where
  exl = nom (mempty :: Support n) exl
  {-# inline exl #-}
  exr = nom (mempty :: Support n) exr
  {-# inline exr #-}
  dup = nom (mempty :: Support n) dup
  {-# inline dup #-}
  it = nom (mempty :: Support n) it
  {-# inline it #-}

class Category k => MonoidalS k where
  (+++)    :: k a b -> k c d -> k (a+c) (b+d)
  left     :: k a b -> k (a+c) (b+c)
  right    :: k c d -> k (a+c) (a+d)
  swapS    :: k (a+b) (b+a)
  lassocS  :: k (a+(b+c)) ((a+b)+c)
  rassocS  :: k ((a+b)+c) (a+(b+c))
  lunitS   :: k (Void+a) a
  lcounitS :: k a (Void+a)
  runitS   :: k (a+Void) a
  rcounitS :: k a (a+Void)

instance MonoidalS (->) where
  (+++) = (Arrow.+++)
  {-# INLINE (+++) #-}
  left = Arrow.left
  {-# INLINE left #-}
  right = Arrow.right
  {-# INLINE right #-}
  swapS = Prelude.either Right Left
  {-# inline swapS #-}
  lassocS (Left a) = Left (Left a)
  lassocS (Right (Left b)) = Left (Right b)
  lassocS (Right (Right c)) = Right c
  {-# inline lassocS #-}
  rassocS (Left (Left a)) = Left a
  rassocS (Left (Right b)) = Right (Left b)
  rassocS (Right c) = Right (Right c)
  {-# inline rassocS #-}
  lunitS = Prelude.either ti id
  {-# inline lunitS #-}
  lcounitS = Right
  {-# inline lcounitS #-}
  runitS = Prelude.either id ti
  {-# inline runitS #-}
  rcounitS = Left
  {-# inline rcounitS #-}

instance IsName n => MonoidalS (Nom n) where
  Nom s f +++ Nom t g = Nom (s <> t) (f +++ g)
  {-# INLINE (+++) #-}
  left (Nom s f) = Nom s (left f)
  {-# INLINE left #-}
  right (Nom s f) = Nom s (right f)
  {-# INLINE right #-}
  swapS = nom (mempty :: Support n) $ Prelude.either Right Left
  {-# inline swapS #-}
  lassocS = nom (mempty :: Support n) lassocS
  {-# inline lassocS #-}
  rassocS = nom (mempty :: Support n) rassocS
  {-# inline rassocS #-}
  lunitS = nom (mempty :: Support n) lunitS
  {-# inline lunitS #-}
  lcounitS = nom (mempty :: Support n) lcounitS
  {-# inline lcounitS #-}
  runitS = nom (mempty :: Support n) runitS
  {-# inline runitS #-}
  rcounitS = nom (mempty :: Support n) rcounitS
  {-# inline rcounitS #-}

instance MonoidalS k => MonoidalS (Op k) where
  Op f +++ Op g = Op (f +++ g)
  {-# inline (+++) #-}
  left (Op f) = Op (left f)
  {-# inline left #-}
  right (Op g) = Op (right g)
  {-# inline right #-}
  swapS = Op swapS
  {-# inline swapS #-}
  lassocS = Op rassocS
  {-# inline lassocS #-}
  rassocS = Op lassocS
  {-# inline rassocS #-}
  lunitS = Op lcounitS
  {-# inline lunitS #-}
  runitS = Op rcounitS
  {-# inline runitS #-}
  lcounitS = Op lunitS
  {-# inline lcounitS #-}
  rcounitS = Op runitS
  {-# inline rcounitS #-}

instance MonoidalS k => MonoidalS (Core k) where
  Core f g +++ Core h i = Core (f +++ h) (g +++ i)
  {-# inline (+++) #-}
  left (Core f g) = Core (left f) (left g)
  {-# inline left #-}
  right (Core f g) = Core (right f) (right g)
  {-# inline right #-}
  swapS = Core swapS swapS
  {-# inline swapS #-}
  lassocS = Core lassocS rassocS
  {-# inline lassocS #-}
  rassocS = Core rassocS lassocS
  {-# inline rassocS #-}
  lunitS = Core lunitS lcounitS
  {-# inline lunitS #-}
  runitS = Core runitS rcounitS
  {-# inline runitS #-}
  lcounitS = Core lcounitS lunitS
  {-# inline lcounitS #-}
  rcounitS = Core rcounitS runitS
  {-# inline rcounitS #-}

class MonoidalS k => Cocartesian k where
  inl      :: k a (a+b)
  inr      :: k b (a+b)
  jam      :: k (a+a) a
  ti       :: k Void a

(|||) :: Cocartesian k => k a c -> k b c -> k (Either a b) c
f ||| g = jam . (f +++ g)

instance Cocartesian (->) where
  inl = Left
  {-# inline inl #-}
  inr = Right
  {-# inline inr #-}
  jam = Prelude.either id id
  {-# inline jam #-}
  ti = absurd
  {-# inline ti #-}

instance IsName n => Cocartesian (Nom n) where
  inl = nom (mempty :: Support n) inl
  {-# inline inl #-}
  inr = nom (mempty :: Support n) inr
  {-# inline inr #-}
  jam = nom (mempty :: Support n) jam
  {-# inline jam #-}
  ti = nom (mempty :: Support n) absurd
  {-# inline ti #-}

class (MonoidalP k, MonoidalS k) => DistributiveCategory k where
  distr :: k ((u+v),b) ((u,b)+(v,b))
  distl :: k (a,(u+v)) ((a,u)+(a,v))

class (MonoidalP k, MonoidalS k) => OpDistributiveCategory k where
  factorl :: k ((a,b)+(a,c)) (a,(b+c))
  default factorl :: (Cartesian k, Cocartesian k) => k ((a,b)+(a,c)) (a,(b+c))
  factorl = second inl ||| second inr
  {-# inline factorl #-}

  factorr :: k ((u,b)+(v,b)) ((u+v),b)
  default factorr :: (Cartesian k, Cocartesian k) => k ((u,b)+(v,b)) ((u+v),b)
  factorr = first inl ||| first inr
  {-# inline factorr #-}

instance OpDistributiveCategory (->)
instance IsName n => OpDistributiveCategory (Nom n)

instance DistributiveCategory (->) where
  distr (Left u,b) = Left (u,b)
  distr (Right v,b) = Right (v,b)
  {-# inline distr #-}
  distl (a,Left u) = Left (a,u)
  distl (a,Right v) = Right (a,v)
  {-# inline distl #-}

instance IsName n => DistributiveCategory (Nom n) where
  distr = nom (mempty :: Support n) distr
  {-# inline distr #-}
  distl = nom (mempty :: Support n) distl
  {-# inline distl #-}

instance OpDistributiveCategory k => DistributiveCategory (Op k) where
  distr = Op factorr
  {-# inline distr #-}
  distl = Op factorl
  {-# inline distl #-}

instance DistributiveCategory k => OpDistributiveCategory (Op k) where
  factorr = Op distr
  {-# inline factorr #-}
  factorl = Op distl
  {-# inline factorl#-}

instance (DistributiveCategory k, OpDistributiveCategory k) => DistributiveCategory (Core k) where
  distr = Core distr factorr
  {-# inline distr #-}
  distl = Core distl factorl
  {-# inline distl #-}

instance (DistributiveCategory k, OpDistributiveCategory k) => OpDistributiveCategory (Core k) where
  factorr = Core factorr distr
  {-# inline factorr #-}
  factorl = Core factorl distl
  {-# inline factorl #-}

class Cartesian k => CCC k where
  apply     :: k (k a b , a) b
  uncurry   :: k a (k b c) -> k (a,b) c
  type Ob k :: Type -> Constraint
  curry     :: Ob k a => k (a,b) c -> k a (k b c)
  const     :: Ob k a => k a (k b a)
  unitArrow :: Ob k a => k a (k () a)

class Trivial a
instance Trivial a

instance CCC (->) where
  type Ob (->) = Trivial
  apply (f,x) = f x
  {-# inline apply #-}
  curry = Prelude.curry
  {-# inline curry #-}
  uncurry = Prelude.uncurry
  {-# inline uncurry #-}
  const     = Prelude.const
  {-# inline const #-}
  unitArrow = Prelude.const
  {-# inline unitArrow #-}

instance IsName n => CCC (Nom n) where
  type Ob (Nom n) = Nominal n
  apply = nom (mempty :: Support n) (uncurry runNom) -- is ok to loose the support of the function here?
  {-# inline apply #-}
  curry (Nom s f) = Nom s $ \a -> Nom (s <> supp a) $ \b -> f (a,b) -- note support of environment
  {-# inline curry #-}
  uncurry (Nom s f) = Nom s $ \(a,b) -> runNom (f a) b
  {-# inline uncurry #-}
  const     = Nom mempty $ \a -> Nom (supp a) (const a)
  {-# inline const #-}
  unitArrow = Nom mempty $ \a -> Nom (supp a) (unitArrow a)
  {-# inline unitArrow #-}

class (IsName n, DistributiveCategory k, OpDistributiveCategory k) => NI n k where
  niso :: Support n -> (a -> b) -> (b -> a) -> k a b

instance IsName n => NI n (->) where
  niso _ f _ = f

instance IsName n => NI n (Nom n) where
  niso s f _ = Nom s f

instance NI n k => NI n (Op k) where
  niso s f g = Op (niso s g f)

instance NI n k => NI n (Core k) where
  niso s f g = Core (niso s f g) (niso s g f)

class (NI n k, CCC k, Cocartesian k) => N n k where
  nom :: Support n -> (a -> b) -> k a b
  con :: proxyn n -> proxyk k -> (k ~ (->) => r) -> r -> r
  nar :: proxyn n -> ((a->b)->(c->d)) -> k a b -> k c d

instance IsName n => N n (->) where
  nom _ = id
  {-# inline nom #-}
  con _ _ x _ = x
  {-# inline con #-}
  nar _ = id

instance IsName n => N n (Nom n) where
  nom = Nom
  {-# inline conlike nom #-}
  con _ _ _ x = x
  {-# inline con #-}
  nar _ k (Nom s f) = Nom s (k f)

-- Nom is not a tensored category over Hask, so we don't get copowers in general, merely finite ones

class Finite a where
  every :: [a]
  default every :: (Bounded a, Enum a) => [a]
  every = [minBound .. maxBound]
  -- add generics here

instance Finite ()
instance Finite Int
instance Finite Bool

instance Finite Void where
  every = []

instance Finite a => Finite (Maybe a) where
  every = Nothing : (Just <$> every)

instance (Finite a, Finite b) => Finite (a, b) where
  every = (,) <$> every <*> every

instance (Finite a, Finite b) => Finite (Either a b) where
  every = fmap Left every <|> fmap Right every

type (⊙) = Tensor
data Tensor v a = Tensor v a -- v should be 'invisible' within Nom, I give no Nom arrows for extracting it
  deriving (Eq, Functor)

instance Permutable n a => Permutable n (Tensor v a) where
  trans i j (Tensor v a) = Tensor v (trans i j a)
  {-# inline trans #-}
  perm p (Tensor v a) = Tensor v (perm p a) -- v many copies of a?
  {-# inline perm #-}

instance IsName n => Permutable1 n (Tensor v) where
  trans1 f i j (Tensor v a) = Tensor v (f i j a)
  {-# inline trans1 #-}
  perm1 f p (Tensor v a) = Tensor v (f p a) -- v many copies of a?
  {-# inline perm1 #-}

instance Nominal n a => Nominal n (Tensor v a) where
  a # Tensor _ b = a # b
  {-# inline (#) #-}
  supp (Tensor _ a) = supp a
  {-# inline supp #-}
  supply (Tensor _ a) = supply a
  {-# inline supply #-}
  equiv (Tensor _ a) = equiv a
  {-# inline equiv #-}

instance IsName n => Nominal1 n (Tensor v) where
  supp1 f (Tensor _ a) = f a
  {-# inline supp1 #-}
  supply1 f (Tensor _ a) = f a
  {-# inline supply1 #-}

instance (Eq a, Binding n b) => Binding n (Tensor a b) where
  binding (Tensor a b) (Tensor c d) = guard (a == c) *> binding b d
  {-# inline binding #-}
  bv (Tensor _ b) = bv b
  {-# inline bv #-}

instance (IsName n, Eq a) => Binding1 n (Tensor a) where
  binding1 f (Tensor a b) (Tensor c d) = guard (a == c) *> f b d
  {-# inline binding1 #-}
  bv1 f (Tensor _ b) = f b
  {-# inline bv1 #-}

class Cartesian k => FinitelyTensored k where -- only needs closed monoidal
  mapTensor :: k a b -> k (v ⊙ a) (v ⊙ b)
  tensor   :: k (v ⊙ a) b -> v -> k a b
  untensor :: Finite v => (v -> k a b) -> k (v ⊙ a) b

instance IsName n => FinitelyTensored (Nom n) where
  mapTensor (Nom s f) = Nom s (fmap f)
  {-# inline mapTensor #-}
  tensor (Nom s f) = Nom s . tensor f
  {-# inline tensor #-}
  untensor f = Nom (foldMap (suppNom . f) every) $ \(Tensor v a) -> runNom (f v) a
  {-# inline untensor #-}

instance FinitelyTensored (->) where
  mapTensor = fmap
  {-# inline mapTensor #-}
  tensor f v = f . Tensor v
  {-# inline tensor #-}
  untensor f (Tensor v a) = f v a
  {-# inline untensor #-}

data Power v a = Power { runPower :: v -> a } deriving Functor
type (⫛) = Power

instance (Finite v, Eq a) => Eq (Power v a) where
  Power f == Power g = fmap f every == fmap g every
  {-# inline (==) #-}

instance Permutable n a => Permutable n (Power v a) where
  trans i j (Power f) = Power (trans i j . f)
  perm p (Power f) = Power (perm p . f)
  {-# inline perm #-}

instance IsName n => Permutable1 n (Power v) where
  trans1 f i j (Power g) = Power (f i j . g)
  perm1 f p (Power g) = Power (f p . g)

instance (Finite v, Nominal n a) => Nominal n (Power v a) where
  a # Power f = Prelude.all ((a #) . f) every
  {-# inline (#) #-}
  supp (Power f) = foldMap (supp . f) every
  {-# inline supp #-}
  supply (Power f) = foldMap (supply . f) every
  {-# inline supply #-}
  -- default supply -- could this be better if i computed sups off of each support instead?
  equiv (Power f) b c = Prelude.all (\ v -> equiv (f v) b c) every
  {-# inline equiv #-}

instance (IsName n, Finite v) => Nominal1 n (Power v) where
  supp1 f (Power g) = foldMap (f . g) every
  {-# inline supp1 #-}
  supply1 f (Power g) = foldMap (f . g) every
  {-# inline supply1 #-}

newtype Applied f a = Applied { getApplied :: f a }
instance (Applicative f, Semigroup a) => Semigroup (Applied f a) where Applied m <> Applied n = Applied $ liftA2 (<>) m n
instance (Applicative f, Monoid a) => Monoid (Applied f a) where mempty = Applied $ pure mempty

instance (Finite a, Binding n b) => Binding n (Power a b) where
  binding (Power f) (Power g) = getApplied $ foldMap (\x -> Applied $ binding (f x) (g x)) every
  {-# inline binding #-}
  bv (Power f) = foldMap (bv . f) every
  {-# inline bv #-}

instance (IsName n, Finite a) => Binding1 n (Power a) where
  binding1 f (Power g) (Power h) = getApplied $ foldMap (\x -> Applied $ f (g x) (h x)) every
  {-# inline binding1 #-}
  bv1 g (Power f) = foldMap (g . f) every
  {-# inline bv1 #-}

instance (Finite a, Irrefutable n b) => Irrefutable n (Power a b) where
  match (Power f) (Power g) = foldMap (\x -> match (f x) (g x)) every
  {-# inline match #-}

instance (IsName n, Finite a) => Irrefutable1 n (Power a) where
  match1 f (Power g) (Power h) = foldMap (\x -> f (g x) (h x)) every
  {-# inline match1 #-}

class Cartesian k => FinitelyPowered k where
  mapPower :: k a b -> k (v ⫛ a) (v ⫛ b)
  power :: k a (v ⫛ b) -> (v -> k a b)
  unpower :: Finite v => (v -> k a b) -> k a (v ⫛ b) -- messy side-condition

instance FinitelyPowered (->) where
  mapPower = fmap
  {-# inline mapPower #-}
  power f v a = runPower (f a) v
  {-# inline power #-}
  unpower f a = Power $ \v -> f v a
  {-# inline unpower #-}

instance IsName n => FinitelyPowered (Nom n) where
  mapPower (Nom s f) = Nom s (fmap f)
  {-# inline mapPower #-}
  power (Nom s f) v = Nom s $ \a -> runPower (f a) v
  {-# inline power #-}
  unpower f = Nom (foldMap (suppNom . f) every) $ \ a -> Power $ \v -> runNom (f v) a
  {-# inline unpower #-}
