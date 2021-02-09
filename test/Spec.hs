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

fromInteger' :: Reifies n Integer => Proxy n -> Integer -> Modulus n
fromInteger' _ = fromInteger

program :: (ReifyComparable s t, Reifies s Integer, Reifies t Integer)
        => Proxy s -> Proxy t -> Integer
program tokenn tokenm = case testSameReification tokenn tokenm of
  Just Refl -> unMod (fromInteger' tokenn 27 + fromInteger' tokenm 29)
  Nothing -> -1

-- Now, for some example uses. Note we *always* use 'doReify' and 'testSameReification', a single way to reflect values
-- of different types.
testIntegerCompare :: Integer -> Integer -> Integer
testIntegerCompare n m =
  reify n $ \tokenn ->
    reify m $ \tokenm ->
      program tokenn tokenm

testCompareTypeable :: Float -> Float -> Bool
testCompareTypeable f g =
  reify (TypeableValue f) $ \tokenf ->
    reify (TypeableValue g) $ \tokeng ->
      isJust (testSameReification tokenf tokenf) && isNothing (testSameReification tokenf tokeng)

main :: IO ()
main = defaultMain $ testGroup "simple reflection"
  [ testCase "reflecting the same value is detected" $ testIntegerCompare 42 42 @?= (27 + 29) `mod` 42
  , testCase "reflecting different values is detected" $ testIntegerCompare 42 43 @?= -1
  , testCase "reflecting typeable works" $ testCompareTypeable 4.2 (-12.3) @? "token comparison is wrong"
  ]
