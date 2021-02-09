{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
import Test.Tasty
import Test.Tasty.HUnit (testCase)
import Test.HUnit

import Data.Proxy (Proxy(..))
import GHC.TypeLits (Nat, KnownNat, natVal)
import Data.Type.Equality ((:~:)(..))
import Data.Reflection.Kinded
import Data.Maybe

newtype Modulus s = Mod { unMod :: Integer }
instance Reifies s Integer => Num (Modulus s) where
  Mod a + Mod b = Mod $ (a + b) `mod` reflect (Proxy :: Proxy s)
  Mod a * Mod b = Mod $ (a * b) `mod` reflect (Proxy :: Proxy s)
  abs (Mod a) = Mod a
  signum (Mod a) = Mod $ if a == 0 then 0 else 1
  fromInteger i = Mod $ i `mod` reflect (Proxy :: Proxy s)
  negate (Mod n) = Mod (reflect (Proxy :: Proxy s) - n)

program :: forall s t. (ReifyComparable s t, Reifies s Integer, Reifies t Integer)
        => Proxy s -> Modulus s -> Proxy t -> Modulus t -> Integer
program tokenn valuen tokenm valuem =
  case testSameReification tokenn tokenm of
    Just Refl -> unMod (valuen + valuem)
    Nothing -> -1

-- Now, for some example uses. Note we *always* use 'doReify' and 'testSameReification', a single way to reflect values
-- of different types.
testIntegerCompare :: Integer -> Integer -> Integer -> Integer -> Integer
testIntegerCompare n m k l =
  reify n $ \tokenn ->
    reify m $ \tokenm ->
      program tokenn (fromInteger k) tokenm (fromInteger l)

testCompareTypeable :: Float -> Float -> Bool
testCompareTypeable f g =
  reify (TypeableValue f) $ \tokenf ->
    reify (TypeableValue g) $ \tokeng ->
      isJust (testSameReification tokenf tokenf) && isNothing (testSameReification tokenf tokeng)

main :: IO ()
main = defaultMain $ testGroup "simple reflection"
  [ testCase "reflecting the same value is detected" $ testIntegerCompare 42 42 27 29 @?= (27 + 29) `mod` 42
  , testCase "reflecting different values is detected" $ testIntegerCompare 42 43 27 29 @?= -1
  , testCase "reflecting typeable works" $ testCompareTypeable 4.2 (-12.3) @? "token comparison is wrong"
  ]
