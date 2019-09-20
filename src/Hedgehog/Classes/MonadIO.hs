{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}

#if MIN_VERSION_base(4,12,0)
{-# LANGUAGE QuantifiedConstraints #-}
#endif

module Hedgehog.Classes.MonadIO (monadIOLaws) where

import Control.Monad.IO.Class (MonadIO(..))

#if MIN_VERSION_base(4,12,0)
#else
import Data.Functor.Classes (Eq1, Show1)
#endif

import Hedgehog
import Hedgehog.Classes.Common

-- | Tests the following 'MonadIO' laws:
--
-- [__Return__]: @'liftIO' '.' 'return'@ ≡ @'return'@
-- [__Lift__]: @'liftIO' (m '>>=' f)@ ≡ @'liftIO' m '>>=' ('liftIO' '.' f)@
#if MIN_VERSION_base(4,12,0)
monadIOLaws ::
  ( MonadIO f
  , forall x. Eq x => Eq (f x), forall x. Show x => Show (f x)
  ) => (forall x. Gen x -> Gen (f x)) -> Laws
#else
monadIOLaws ::
  ( MonadIO f
  , Eq1 f, Show1 f
  ) => (forall x. Gen x -> Gen (f x)) -> Laws
#endif
monadIOLaws gen = Laws "MonadIO"
  [ ("Return", monadIOReturn gen)
  , ("Lift", monadIOLift gen)
  ]

#if MIN_VERSION_base(4,12,0)
type MonadIOProp f =
  ( MonadIO f
  , forall x. Eq x => Eq (f x), forall x. Show x => Show (f x)
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#else
type MonadIOProp f =
  ( MonadIO f
  , Eq1 f, Show1 f
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#endif

monadIOReturn :: forall f. MonadIOProp f
monadIOReturn _fgen = property $ do
  x <- forAll genSmallInteger
  let lhs = liftIO (return x)
  let rhs = return x :: f Integer
  let ctx = contextualise $ LawContext
        { lawContextLawName = "Return", lawContextTcName = "MonadIO"
        , lawContextLawBody = "liftIO . return" `congruency` "return"
        , lawContextReduced = reduced lhs rhs
        , lawContextTcProp =
            let showX = show x
            in lawWhere
              [ "liftIO . return $ x" `congruency` "return x, where"
              , "x = " ++ showX
              ]
        }
  heqCtx1 lhs rhs ctx

monadIOLift :: forall f. MonadIOProp f
monadIOLift _fgen = property $ do
  m <- forAllWith showIO $ genIO genSmallInteger
  f' <- forAll genLinearEquation
  let f = pure . runLinearEquation f'
  let lhs = liftIO (m >>= f) :: f Integer
  let rhs = liftIO m >>= (liftIO . f) :: f Integer
  let ctx = contextualise $ LawContext
        { lawContextLawName = "Lift", lawContextTcName = "MonadIO"
        , lawContextLawBody = "liftIO (m >>= f)" `congruency` "liftIO m >>= (liftIO . f)"
        , lawContextReduced = reduced lhs rhs
        , lawContextTcProp =
            let showM = showIO m
                showF = show f'
            in lawWhere
              [ "liftIO (m >>= f)" `congruency` "liftIO m >>= (liftIO . f), where"
              , "f = " ++ showF
              , "m = " ++ showM
              ]
        }
  heqCtx1 lhs rhs ctx
