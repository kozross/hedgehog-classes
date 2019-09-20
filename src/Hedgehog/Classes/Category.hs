{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}

#if MIN_VERSION_base(4,12,0)
{-# LANGUAGE QuantifiedConstraints #-}
#endif

module Hedgehog.Classes.Category (categoryLaws, commutativeCategoryLaws) where

import Hedgehog
import Hedgehog.Classes.Common

#if MIN_VERSION_base(4,12,0)
#else
import Data.Functor.Classes (Eq2, Show2)
#endif

import Control.Category(Category(..))
import Prelude hiding (id, (.))

-- | Tests the following 'Category' laws:
--
-- [__Left Identity__]: @'id' '.' f@ ≡ @f@
-- [__Right Identity__]: @f '.' 'id'@ ≡ @f@
-- [__Associativity__]: @f '.' (g '.' h)@ ≡ @(f '.' g) '.' h@
#if MIN_VERSION_base(4,12,0)
categoryLaws :: forall f.
  ( Category f
  , forall x y. (Eq x, Eq y) => Eq (f x y)
  , forall x y. (Show x, Show y) => Show (f x y)
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Laws
#else
categoryLaws :: forall f.
  ( Category f
  , Eq2 f
  , Show2 f
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Laws
#endif
categoryLaws gen = Laws "Category"
  [ ("Left Identity", categoryLeftIdentity gen)
  , ("Right Identity", categoryRightIdentity gen)
  , ("Associativity", categoryAssociativity gen)
  ]

-- | Tests the following 'Category' laws:
--
-- [__Commutativity__]: @f '.' g@ ≡ @g '.' f@
#if MIN_VERSION_base(4,12,0)
commutativeCategoryLaws :: forall f.
  ( Category f
  , forall x y. (Eq x, Eq y) => Eq (f x y)
  , forall x y. (Show x, Show y) => Show (f x y)
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Laws
#else
commutativeCategoryLaws :: forall f.
  ( Category f
  , Eq2 f
  , Show2 f
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Laws
#endif
commutativeCategoryLaws gen = Laws "Commutative Category"
  [ ("Commutativity", categoryCommutativity gen)
  ]

#if MIN_VERSION_base(4,12,0)
categoryRightIdentity :: forall f.
  ( Category f
  , forall x y. (Eq x, Eq y) => Eq (f x y)
  , forall x y. (Show x, Show y) => Show (f x y)
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Property
#else
categoryRightIdentity :: forall f.
  ( Category f
  , Eq2 f
  , Show2 f
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Property
#endif
categoryRightIdentity fgen = property $ do
  x <- forAll $ fgen genSmallInteger genSmallInteger
  (x . id) `heq2` x

#if MIN_VERSION_base(4,12,0)
categoryLeftIdentity :: forall f.
  ( Category f
  , forall x y. (Eq x, Eq y) => Eq (f x y)
  , forall x y. (Show x, Show y) => Show (f x y)
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Property
#else
categoryLeftIdentity :: forall f.
  ( Category f
  , Eq2 f
  , Show2 f
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Property
#endif
categoryLeftIdentity fgen = property $ do
  x <- forAll $ fgen genSmallInteger genSmallInteger
  (id . x) `heq2` x

#if MIN_VERSION_base(4,12,0)
categoryAssociativity :: forall f.
  ( Category f
  , forall x y. (Eq x, Eq y) => Eq (f x y)
  , forall x y. (Show x, Show y) => Show (f x y)
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Property
#else
categoryAssociativity :: forall f.
  ( Category f
  , Eq2 f
  , Show2 f
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Property
#endif
categoryAssociativity fgen = property $ do
  f <- forAll $ fgen genSmallInteger genSmallInteger
  g <- forAll $ fgen genSmallInteger genSmallInteger 
  h <- forAll $ fgen genSmallInteger genSmallInteger 
  (f . (g . h)) `heq2` ((f . g) . h)

#if MIN_VERSION_base(4,12,0)
categoryCommutativity :: forall f.
  ( Category f
  , forall x y. (Eq x, Eq y) => Eq (f x y)
  , forall x y. (Show x, Show y) => Show (f x y)
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Property
#else
categoryCommutativity :: forall f.
  ( Category f
  , Eq2 f
  , Show2 f
  ) => (forall x y. Gen x -> Gen y -> Gen (f x y)) -> Property
#endif
categoryCommutativity fgen = property $ do
  f <- forAll $ fgen genSmallInteger genSmallInteger
  g <- forAll $ fgen genSmallInteger genSmallInteger
  (f . g) `heq2` (g . f)
