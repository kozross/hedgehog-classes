{-# LANGUAGE CPP #-}

#if MIN_VERSION_base(4,12,0)
{-# LANGUAGE QuantifiedConstraints #-}
#endif

module Hedgehog.Classes.Common.Compat
  ( readMaybe
  , eq
  , eq1
  , eq2

  , show1
  , show2

  , neq
  , neq1
  , neq2
  ) where

import Text.Read (readMaybe)

#if MIN_VERSION_base(4,12,0)
#else
import Data.Functor.Classes (Eq1(..), Eq2(..), Show1(..), Show2(..))
#endif

eq :: Eq a => a -> a -> Bool
eq = (==)

neq :: Eq a => a -> a -> Bool
neq = (/=)

#if MIN_VERSION_base(4,12,0)
eq1 :: (Eq a, forall x. Eq x => Eq (f x)) => f a -> f a -> Bool
eq1 = (==)

neq1 :: (Eq a, forall x. Eq x => Eq (f x)) => f a -> f a -> Bool
neq1 = (/=)

eq2 :: (Eq a, Eq b, forall x y. (Eq x, Eq y) => Eq (f x y)) => f a b -> f a b -> Bool
eq2 = (==)

neq2 :: (Eq a, Eq b, forall x y. (Eq x, Eq y) => Eq (f x y)) => f a b -> f a b -> Bool
neq2 = (/=)

show1 :: (Show a, forall x. (Show x) => Show (f x)) => f a -> String
show1 = Prelude.show

show2 :: (Show a, Show b, forall x y. (Show x, Show y) => Show (f x y)) => f a b -> String
show2 = Prelude.show

#else
eq1 :: (Eq a, Eq1 f) => f a -> f a -> Bool
eq1 = liftEq (==)

neq1 :: (Eq a, Eq1 f) => f a -> f a -> Bool
neq1 = liftEq (/=)

eq2 :: (Eq a, Eq b, Eq2 f) => f a b -> f a b -> Bool
eq2 = liftEq2 (==) (==)

neq2 :: (Eq a, Eq b, Eq2 f) => f a b -> f a b -> Bool
neq2 = liftEq2 (/=) (/=)

show1 :: (Show a, Show1 f) => f a -> String
show1 = ($ "") . liftShowsPrec showsPrec showList 0

show2 :: (Show a, Show b, Show2 f) => f a b -> String
show2 = ($ "") . liftShowsPrec2 showsPrec showList showsPrec showList 0
#endif





