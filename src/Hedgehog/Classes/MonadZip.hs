{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}

#if MIN_VERSION_base(4,12,0)
{-# LANGUAGE QuantifiedConstraints #-}
#endif

module Hedgehog.Classes.MonadZip (monadZipLaws) where

import Control.Arrow (Arrow(..))
import Control.Monad.Zip (MonadZip(mzip))

#if MIN_VERSION_base(4,12,0)
#else
import Data.Functor.Classes (Eq1, Show1)
#endif

import Hedgehog
import Hedgehog.Classes.Common

-- | Tests the following 'MonadZip' laws:
--
-- [__Naturality__]: @'fmap' (f '***' g) ('mzip' ma mb)@ ≡ @'mzip' ('fmap' f ma) ('fmap' g mb)@
#if MIN_VERSION_base(4,12,0)
monadZipLaws ::
  ( MonadZip f
  , forall x. Eq x => Eq (f x), forall x. Show x => Show (f x)
  ) => (forall x. Gen x -> Gen (f x)) -> Laws
#else
monadZipLaws ::
  ( MonadZip f
  , Eq1 f, Show1 f
  ) => (forall x. Gen x -> Gen (f x)) -> Laws
#endif
monadZipLaws gen = Laws "Monad"
  [ ("Naturality", monadZipNaturality gen)
  ]

#if MIN_VERSION_base(4,12,0)
type MonadZipProp f =
  ( MonadZip f
  , forall x. Eq x => Eq (f x), forall x. Show x => Show (f x)
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#else
type MonadZipProp f =
  ( MonadZip f
  , Eq1 f, Show1 f
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#endif

monadZipNaturality :: forall f. MonadZipProp f
monadZipNaturality fgen = property $ do
  f' <- forAll genLinearEquation
  g' <- forAll genLinearEquation
  let f = runLinearEquation f'
      g = runLinearEquation g'
  ma <- forAll $ fgen genSmallInteger
  mb <- forAll $ fgen genSmallInteger
  let lhs = fmap (f *** g) (mzip ma mb)
  let rhs = mzip (fmap f ma) (fmap g mb)
  let ctx = contextualise $ LawContext
        { lawContextLawName = "Naturality", lawContextTcName = "MonadZip"
        , lawContextLawBody = "(fmap (f *** g) (mzip ma mb)" `congruency` "mzip (fmap f ma) (fmap g mb)"
        , lawContextReduced = reduced lhs rhs
        , lawContextTcProp =
            let showF = show f'; showG = show g'; showMA = show ma; showMB = show mb;
            in lawWhere
              [ "fmap (f *** g) (mzip ma mb)" `congruency` "mzip (fmap f ma) (fmap g mb), where"
              , "f = " ++ showF
              , "g = " ++ showG
              , "ma = " ++ showMA  
              , "mb = " ++ showMB
              ]
        }
  heqCtx1 lhs rhs ctx
