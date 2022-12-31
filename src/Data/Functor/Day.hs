{-# LANGUAGE CPP #-}
#include "kan-extensions-common.h"
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}

-----------------------------------------------------------------------------

----------------------------------------------------------------------------

{- |
Copyright   :  (C) 2014-2016 Edward Kmett
License     :  BSD-style (see the file LICENSE)

Maintainer  :  Edward Kmett <ekmett@gmail.com>
Stability   :  provisional
Portability :  portable

Eitan Chatav first introduced me to this construction

The Day convolution of two covariant functors is a covariant functor.

Day convolution is usually defined in terms of contravariant functors,
however, it just needs a monoidal category, and Hask^op is also monoidal.

Day convolution can be used to nicely describe monoidal functors as monoid
objects w.r.t this product.

<http://ncatlab.org/nlab/show/Day+convolution>
-}
module Data.Functor.Day (
  Day (..),
  day,
  dap,
  assoc,
  disassoc,
  swapped,
  intro1,
  intro2,
  elim1,
  elim2,
  trans1,
  trans2,
  cayley,
  dayley,
) where

import Control.Applicative
import Control.Category
import Control.Comonad
import Control.Comonad.Trans.Class
import Data.Distributive
import Data.Functor.Classes.Compat
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Profunctor.Cayley (Cayley (..))
import Data.Profunctor.Composition (Procompose (..))
import Data.Functor.Adjunction
import Data.Foldable
import Data.Semigroup.Foldable
import Data.Traversable
import Data.Semigroup.Traversable

import qualified Data.Array as Arr
#ifdef __GLASGOW_HASKELL__
import Data.Typeable
#endif
import Prelude hiding (id, (.), foldr)
import Data.Monoid (Sum(..))


-- | The Day convolution of two covariant functors.
data Day f g a = forall b c. Day (f b) (g c) (b -> c -> a)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
  deriving Typeable
#endif

-- | Construct the Day convolution
day :: f (a -> b) -> g a -> Day f g b
day fa gb = Day fa gb id

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 707
instance (Typeable1 f, Typeable1 g) => Typeable1 (Day f g) where
    typeOf1 tfga = mkTyConApp dayTyCon [typeOf1 (fa tfga), typeOf1 (ga tfga)]
        where fa :: t f (g :: * -> *) a -> f a
              fa = undefined
              ga :: t (f :: * -> *) g a -> g a
              ga = undefined

dayTyCon :: TyCon
#if MIN_VERSION_base(4,4,0)
dayTyCon = mkTyCon3 "contravariant" "Data.Functor.Day" "Day"
#else
dayTyCon = mkTyCon "Data.Functor.Day.Day"
#endif

#endif

instance Functor (Day f g) where
  fmap f (Day fb gc bca) = Day fb gc $ \b c -> f (bca b c)

instance (Applicative f, Applicative g) => Applicative (Day f g) where
  pure x = Day (pure ()) (pure ()) (\_ _ -> x)
  (Day fa fb u) <*> (Day gc gd v) =
    Day
      ((,) <$> fa <*> gc)
      ((,) <$> fb <*> gd)
      (\(a, c) (b, d) -> u a b (v c d))

instance (Representable f, Representable g) => Distributive (Day f g) where
  distribute f = Day (tabulate id) (tabulate id) $ \x y ->
    fmap (\(Day m n o) -> o (index m x) (index n y)) f

  collect g f = Day (tabulate id) (tabulate id) $ \x y ->
    fmap (\q -> case g q of Day m n o -> o (index m x) (index n y)) f

instance (Representable f, Representable g) => Representable (Day f g) where
  type Rep (Day f g) = (Rep f, Rep g)
  tabulate f = Day (tabulate id) (tabulate id) (curry f)
  index (Day m n o) (x, y) = o (index m x) (index n y)

instance (Adjunction f u, Adjunction f' u') => Adjunction (Day f f') (Day u u') where
  unit a = Day (unit ()) (unit ()) (\f f' -> Day f f' (\() () -> a))
  counit (Day f f' h) = case h a a' of Day u u' g -> g (indexAdjunction u f_) (indexAdjunction u' f_')
    where
      (a, f_) = splitL f
      (a', f_') = splitL f'
  
instance (Comonad f, Comonad g) => Comonad (Day f g) where
  extract (Day fb gc bca) = bca (extract fb) (extract gc)
  duplicate (Day fb gc bca) = Day (duplicate fb) (duplicate gc) (\fb' gc' -> Day fb' gc' bca)

instance (ComonadApply f, ComonadApply g) => ComonadApply (Day f g) where
  Day fa fb u <@> Day gc gd v =
    Day
      ((,) <$> fa <@> gc)
      ((,) <$> fb <@> gd)
      (\(a, c) (b, d) -> u a b (v c d))

instance Comonad f => ComonadTrans (Day f) where
  lower (Day fb gc bca) = bca (extract fb) <$> gc

liftEqDay ::
#ifdef LIFTED_FUNCTOR_CLASSES
     (Eq1 f, Eq1 g)
#else
     (Eq1 f, Functor f, Eq1 g, Functor g)
#endif
  => (a -> b -> Bool) -> Day f g a -> Day f g b -> Bool
liftEqDay eq (Day f1 g1 op1) (Day f2 g2 op2)
  | emptyEq f1 f2 = boringEq g1 g2
  | otherwise = liftEq (\a1 a2 -> liftEq (\b1 b2 -> eq (op1 a1 b1) (op2 a2 b2)) g1 g2) f1 f2

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Eq1 f, Eq1 g) => Eq1 (Day f g) where
  liftEq = liftEqDay

instance (Eq1 f, Eq1 g, Eq a) => Eq (Day f g a) where
  (==) = eq1
#else
instance (Eq1 f, Functor f, Eq1 g, Functor g) => Eq1 (Day f g) where
  eq1 = liftEqDay (==)

instance (Eq1 f, Functor f, Eq1 g, Functor g, Eq a) => Eq (Day f g a) where
  (==) = eq1
#endif

liftCompareDay ::
#ifdef LIFTED_FUNCTOR_CLASSES
     (Ord1 f, Ord1 g)
#else
     (Ord1 f, Functor f, Ord1 g, Functor g)
#endif
  => (a -> b -> Ordering) -> Day f g a -> Day f g b -> Ordering
liftCompareDay cmp (Day f1 g1 op1) (Day f2 g2 op2)
  | emptyEq f1 f2 = boringCompare g1 g2
  | otherwise = liftCompare (\a1 a2 -> liftCompare (\b1 b2 -> cmp (op1 a1 b1) (op2 a2 b2)) g1 g2) f1 f2

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Ord1 f, Ord1 g) => Ord1 (Day f g) where
  liftCompare = liftCompareDay

instance (Ord1 f, Ord1 g, Ord a) => Ord (Day f g a) where
  compare = compare1
#else
instance (Ord1 f, Functor f, Ord1 g, Functor g) => Ord1 (Day f g) where
  compare1 = liftCompareDay compare

instance (Ord1 f, Functor f, Ord1 g, Functor g, Ord a) => Ord (Day f g a) where
  compare = compare1
#endif

-- | @'toList' == 'dap' . 'trans1' toList . 'trans2' toList@
instance (Foldable f, Foldable g) => Foldable (Day f g) where
  foldMap h (Day f g op) = foldMap (\a -> foldMap (\b -> h (op a b)) g) f
  foldr step zero (Day f g op) = foldr (\a r -> foldr (\b -> step (op a b)) r g) zero f
  
#if MIN_VERSION_base(4,8,0)
  null (Day f g _) = null f || null g

  length :: (Foldable f, Foldable g) => Day f g a -> Int
  length (Day f g _) = length f * length g
#endif

instance (Foldable1 f, Foldable1 g) => Foldable1 (Day f g) where
  foldMap1 h (Day f g op) = foldMap1 (\a -> foldMap1 (\b -> h (op a b)) g) f

testEmpty :: Traversable f => f a -> Maybe (f b)
testEmpty = traverse (const Nothing)

indices :: Traversable f => f a -> f Int
indices = snd . mapAccumL (\n _ -> n `seq` (n+1, n)) 0

length' :: Foldable f => f a -> Int
#if MIN_VERSION_base(9,8,0)
length' = length
#else
length' = getSum . foldMap (const (Sum 1))
#endif

instance (Traversable f, Traversable g) => Traversable (Day f g) where
  -- Note on the implementation of traverse (Day f g)
  -- 
  --  This implementation first checks if either f or g is null,
  -- and takes a fast path if it is.
  --
  --  The benefit of this check is skipping the traversal of the
  -- other (not found to be null) functor to save time and memory,
  -- used to keep unnecessary indices.
  -- 
  --  Most of the time, the @testEmpty@ check is cheap.
  -- For example, @testEmpty@ is @O(1)@ on @[]@ or @Array i@.
  
  traverse h (Day f g op) = case (testEmpty f, testEmpty g) of
      (Just fAny, _) -> pure (Day fAny g const)
      (_, Just gAny) -> pure (Day f gAny (\_ v -> v))
      _ ->
        let fi = indices f
            gj = indices g
            idx a i j = a Arr.! (lenG * i + j)
            makeArray = Arr.listArray (0, lenF * lenG - 1)
            fromTable cs = Day fi gj (idx (makeArray cs))
        in fromTable <$> traverse h (op <$> toList f <*> toList g)
      where
        lenF = length' f
        lenG = length' g

instance (Traversable1 f, Traversable1 g) => Traversable1 (Day f g) where
  traverse1 h (Day f g op) =
    let fi = indices f
        gj = indices g
        idx a i j = a Arr.! (lenG * i + j)
        makeArray = Arr.listArray (0, lenF * lenG - 1) . toList
        fromTable cs = Day fi gj (idx (makeArray cs))
    in fromTable <$> traverse1 h (op <$> toNonEmpty f <*> toNonEmpty g)
      where
        lenF = length' f
        lenG = length' g

{- | Day convolution provides a monoidal product. The associativity
of this monoid is witnessed by 'assoc' and 'disassoc'.

@
'assoc' . 'disassoc' = 'id'
'disassoc' . 'assoc' = 'id'
'fmap' f '.' 'assoc' = 'assoc' '.' 'fmap' f
@
-}
assoc :: Day f (Day g h) a -> Day (Day f g) h a
assoc (Day fb (Day gd he dec) bca) = Day (Day fb gd (,)) he $
  \(b, d) e -> bca b (dec d e)

{- | Day convolution provides a monoidal product. The associativity
of this monoid is witnessed by 'assoc' and 'disassoc'.

@
'assoc' . 'disassoc' = 'id'
'disassoc' . 'assoc' = 'id'
'fmap' f '.' 'disassoc' = 'disassoc' '.' 'fmap' f
@
-}
disassoc :: Day (Day f g) h a -> Day f (Day g h) a
disassoc (Day (Day fb gc bce) hd eda) = Day fb (Day gc hd (,)) $ \b (c, d) ->
  eda (bce b c) d

{- | The monoid for 'Day' convolution on the cartesian monoidal structure is symmetric.

@
'fmap' f '.' 'swapped' = 'swapped' '.' 'fmap' f
@
-}
swapped :: Day f g a -> Day g f a
swapped (Day fb gc abc) = Day gc fb (flip abc)

{- | 'Identity' is the unit of 'Day' convolution

@
'intro1' '.' 'elim1' = 'id'
'elim1' '.' 'intro1' = 'id'
@
-}
intro1 :: f a -> Day Identity f a
intro1 fa = Day (Identity ()) fa $ \_ a -> a

{- | 'Identity' is the unit of 'Day' convolution

@
'intro2' '.' 'elim2' = 'id'
'elim2' '.' 'intro2' = 'id'
@
-}
intro2 :: f a -> Day f Identity a
intro2 fa = Day fa (Identity ()) const

{- | 'Identity' is the unit of 'Day' convolution

@
'intro1' '.' 'elim1' = 'id'
'elim1' '.' 'intro1' = 'id'
@
-}
elim1 :: Functor f => Day Identity f a -> f a
elim1 (Day (Identity b) fc bca) = bca b <$> fc

{- | 'Identity' is the unit of 'Day' convolution

@
'intro2' '.' 'elim2' = 'id'
'elim2' '.' 'intro2' = 'id'
@
-}
elim2 :: Functor f => Day f Identity a -> f a
elim2 (Day fb (Identity c) bca) = flip bca c <$> fb

{- | Collapse via a monoidal functor.

@
'dap' ('day' f g) = f '<*>' g
@
-}
dap :: Applicative f => Day f f a -> f a
dap (Day fb fc abc) = liftA2 abc fb fc

{- | Apply a natural transformation to the left-hand side of a Day convolution.

This respects the naturality of the natural transformation you supplied:

@
'fmap' f '.' 'trans1' fg = 'trans1' fg '.' 'fmap' f
@
-}
trans1 :: (forall x. f x -> g x) -> Day f h a -> Day g h a
trans1 fg (Day fb hc bca) = Day (fg fb) hc bca

{- | Apply a natural transformation to the right-hand side of a Day convolution.

This respects the naturality of the natural transformation you supplied:

@
'fmap' f '.' 'trans2' fg = 'trans2' fg '.' 'fmap' f
@
-}
trans2 :: (forall x. g x -> h x) -> Day f g a -> Day f h a
trans2 gh (Day fb gc bca) = Day fb (gh gc) bca

cayley :: Procompose (Cayley f p) (Cayley g q) a b -> Cayley (Day f g) (Procompose p q) a b
cayley (Procompose (Cayley p) (Cayley q)) = Cayley $ Day p q Procompose

-- | Proposition 4.1 from Pastro and Street
dayley :: Category p => Procompose (Cayley f p) (Cayley g p) a b -> Cayley (Day f g) p a b
dayley (Procompose (Cayley p) (Cayley q)) = Cayley $ Day p q (.)
