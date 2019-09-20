{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}

#if MIN_VERSION_base(4,12,0)
{-# LANGUAGE QuantifiedConstraints #-}
#endif

module Hedgehog.Classes.Functor (functorLaws) where

import Hedgehog
import Hedgehog.Classes.Common

#if MIN_VERSION_base(4,12,0)
#else
import Data.Functor.Classes (Eq1, Show1)
#endif

-- | Tests the following 'Functor' laws:
--
-- [__Identity__]: @'fmap' 'id'@ ≡ @'id'@
-- [__Composition__]: @'fmap' f '.' 'fmap' g@ ≡ @'fmap' (f '.' g)@
-- [__Const__]: @'fmap' ('const' x)@ ≡ @x '<$'@
#if MIN_VERSION_base(4,12,0)
functorLaws ::
  ( Functor f
  , forall x. Eq x => Eq (f x), forall x. Show x => Show (f x)
  ) => (forall x. Gen x -> Gen (f x)) -> Laws
#else
functorLaws ::
  ( Functor f
  , Eq1 f, Show1 f
  ) => (forall x. Gen x -> Gen (f x)) -> Laws
#endif
functorLaws gen = Laws "Functor"
  [ ("Identity", functorIdentity gen)
  , ("Composition", functorComposition gen)
  , ("Const", functorConst gen)
  ]

#if MIN_VERSION_base(4,12,0)
functorIdentity ::
  ( Functor f
  , forall x. Eq x => Eq (f x), forall x. Show x => Show (f x)
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#else
functorIdentity ::
  ( Functor f
  , Eq1 f, Show1 f
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#endif
functorIdentity fgen = property $ do
  a <- forAll $ fgen genSmallInteger
  let lhs = fmap id a
  let rhs = id a
  let ctx = contextualise $ LawContext
        { lawContextLawName = "Identity", lawContextTcName = "Functor"
        , lawContextLawBody = "fmap id" `congruency` "id"
        , lawContextTcProp =
            let showA = show a
            in lawWhere
              [ "fmap id a" `congruency` "id a, where"
              , "a = " ++ showA
              ]
        , lawContextReduced = reduced lhs rhs
        } 
  heqCtx lhs rhs ctx

#if MIN_VERSION_base(4,12,0)
functorComposition ::
  ( Functor f
  , forall x. Eq x => Eq (f x), forall x. Show x => Show (f x)
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#else
functorComposition ::
  ( Functor f
  , Eq1 f, Show1 f
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#endif
functorComposition fgen = property $ do
  a <- forAll $ fgen genSmallInteger
  let f = func2; g = func1 
  let lhs = fmap f (fmap g a)
  let rhs = fmap (f . g) a
  let ctx = contextualise $ LawContext
        { lawContextLawName = "Composition", lawContextTcName = "Functor"
        , lawContextLawBody = "fmap f . fmap g" `congruency` "fmap (f . g)"
        , lawContextTcProp =
            let showA = show a
                showF = "\\(a,b) -> (odd a, if even a then Left (compare a b) else Right (b + 2)"
                showG = "\\i -> (div (i + 5) 3, i * i - 2 * i + 1)"
            in lawWhere
              [ "fmap f . fmap g $ a" `congruency` "fmap (f . g) a, where"
              , "f = " ++ showF
              , "g = " ++ showG
              , "a = " ++ showA
              ]
        , lawContextReduced = reduced lhs rhs
        }
  heqCtx lhs rhs ctx

#if MIN_VERSION_base(4,12,0)
functorConst ::
  ( Functor f
  , forall x. Eq x => Eq (f x), forall x. Show x => Show (f x)
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#else
functorConst ::
  ( Functor f
  , Eq1 f, Show1 f
  ) => (forall x. Gen x -> Gen (f x)) -> Property
#endif
functorConst fgen = property $ do
  a <- forAll $ fgen genSmallInteger
  let x = 'X'
  let lhs = fmap (const x) a
  let rhs = x <$ a
  let ctx = contextualise $ LawContext
        { lawContextLawName = "Const", lawContextTcName = "Functor"
        , lawContextLawBody = "fmap (const x)" `congruency` "x <$"
        , lawContextTcProp =
            let showA = show a
                showX = show x
            in lawWhere
              [ "fmap (const x) a" `congruency` "x <$ a, where"
              , "x = " ++ showX
              , "a = " ++ showA
              ]
        , lawContextReduced = reduced lhs rhs
        }
  heqCtx lhs rhs ctx
