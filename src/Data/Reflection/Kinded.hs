-- | This module exports a generic 'reify' method where the type of the argument determines the kind
-- of the reflecting proxy. For example, reifying a 'Integer' is reflected by a @KnownNat (n :: Nat)@.
--
-- Users of 'Data.Reflection' can change their calls to 'R.reify' to @reify . GenericValue@ and their
-- calls to 'reifyTypeable' to @reify . TypeableValue@. Further, 'reifyNat' and 'reifySymbol' are
-- subsumbed by writing simply 'reify'.
--
-- A major influence on the decision to unify the class of reifiable values is that some kinds, e.g.
-- 'Nat' and 'Symbol', are instances of the provided 'KindComparable'. It is thus possible to discover
-- that two reflecting variables, say @s@ and @t@, are reflecting the same value, via matching on
-- a @testSameReification proxys proxy t :: Maybe (s :~: t)@.
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Reflection.Kinded
( ReifyKind
, ReifyConstraint
, Reifiable(..)
, GenericValue(..)
, AKind
, KnownKind
, TypeableValue(..)
, KindComparable(..)
, ReifyComparable
, testSameReification
, module ReflReexport
)
where

import Data.Reflection as ReflReexport (give, Given(..), Reifies(..))
import Data.Reflection (reifyNat, reifySymbol, reifyTypeable)
import Data.Reflection as IR (reify)
import Data.Proxy (Proxy(..))
import Data.Kind (Type, Constraint)
import Data.Coerce (coerce)
import Data.Typeable (eqT)
import Data.Type.Equality ((:~:)(..), testEquality)
import Type.Reflection as Refl

import GHC.TypeLits (Nat, Symbol, sameNat, KnownNat, sameSymbol, KnownSymbol, natVal, TypeError, ErrorMessage(..))
import GHC.Prim (Proxy#, proxy#)
import GHC.Exts (TYPE, RuntimeRep(TupleRep))

-- | The kind of the variable that reflects a value
type family ReifyKind a
type instance ReifyKind Integer = Nat
type instance ReifyKind String = Symbol

-- | The constraint placed on the reflecting variable
type family ReifyConstraint a :: ReifyKind a -> Constraint
type instance ReifyConstraint Integer = KnownNat
type instance ReifyConstraint String = KnownSymbol

-- | Class of values that might be reified. In a universally quantified context
-- over a new type variable of kind @ReifyKind a@, a result can be computed.
--
-- Note: although it is not enforced by this type class, usually the reified value
-- can be accessed through 'reflect', since @forall s. ReifyConstraint a s :- Reifies s a@
-- is expected.
class Reifiable a where
  reify :: a -> (forall s. ReifyConstraint a s => Proxy s -> r) -> r

instance Reifiable Integer where
  reify = reifyNat

instance Reifiable String where
  reify = reifySymbol

-- | 'GenericValue' is reflected by a mere 'Type' variable, that can be reflected back to the value.
-- These type variables can not be compared for equality, making them lightweight, but also less useful.
newtype GenericValue a = GenericValue a
class Reifies s a => Refries a s
instance Reifies s a => Refries a s
type instance ReifyKind (GenericValue a) = Type
type instance ReifyConstraint (GenericValue a) = Refries a

instance Reifiable (GenericValue a) where
  reify (GenericValue a) = IR.reify a

-- | Kind of variables used to reflect a 'TypeableValue'. Internally wraps a type variable
-- that is known to be 'Typeable' and can thus be compared for equality.
newtype AKind (a :: Type) = AKind Type
data KindInspect (k :: AKind a) =
  forall s. (Typeable s, Reifies s a, k ~ 'AKind s) => KindInspect (Proxy# s)

-- | A 'KnownKind (k :: AKind a)' reflects the fact 'Typeable a' and can also 'reflect' back the value.
class KnownKind (k :: AKind a) where
  inspectKind :: KindInspect k

instance forall a s. (Typeable s, Reifies s a) => KnownKind ('AKind s :: AKind a) where
  inspectKind = KindInspect (proxy# :: Proxy# s)

instance KnownKind (k :: AKind a) => Reifies k a where
  reflect _ = case (inspectKind :: KindInspect k) of KindInspect (p :: Proxy# s) -> reflect (Proxy :: Proxy s)

-- | A 'TypeableValue' is reflected a 'AKind' variable, which can be tested for equality by 'testSameReification'.
newtype TypeableValue a = TypeableValue a
class (KnownKind k) => ReifyTypeable a (k :: AKind a)
instance (KnownKind k) => ReifyTypeable a k
-- ^ when simplying using KnownKind in the instance declaration of ReifyConstraint,
-- ghc complains. Putting this on top silences it.

type instance ReifyKind (TypeableValue a) = AKind a
type instance ReifyConstraint (TypeableValue a) = ReifyTypeable a

instance Typeable a => Reifiable (TypeableValue a) where
  reify (TypeableValue a) f = reifyTypeable a $ \(_ :: Proxy s) -> f (Proxy :: Proxy ('AKind s))

-- | Some kinds, like 'Nat', can be conditionally tested for equality. Note the similarity to 'Data.Type.Equality.TestEquality'.
class KindComparable k where
  type KindEqualityCon k :: k -> Constraint
  testEqualityOnKind :: (KindEqualityCon k s, KindEqualityCon k t) => Maybe (s :~: t)

type ReifyComparable (s :: k) (t :: k) = (KindComparable k, KindEqualityCon k s, KindEqualityCon k t)

-- | The same as 'testEqualityOnKind', but with explicit proxy arguments which can be used as type hints.
testSameReification
  :: (ReifyComparable s t)
  => proxy s -> proxy t -> Maybe (s :~: t)
testSameReification _ _ = testEqualityOnKind
{-# INLINE testSameReification #-}

instance KindComparable Nat where
  type KindEqualityCon Nat = KnownNat
  testEqualityOnKind = sameNat Proxy Proxy

instance KindComparable Symbol where
  type KindEqualityCon Symbol = KnownSymbol
  testEqualityOnKind = sameSymbol Proxy Proxy

instance KindComparable (AKind a) where
  type KindEqualityCon (AKind a) = KnownKind
  testEqualityOnKind :: forall m n. (KnownKind m, KnownKind n) => Maybe (m :~: n)
  testEqualityOnKind = case (inspectKind :: KindInspect m, inspectKind :: KindInspect n) of
    (KindInspect ps, KindInspect pt) -> case eqTProxy ps pt of
      Just Refl -> Just Refl
      Nothing -> Nothing

-- An instance for 'Type' is explicitly *not* provided. 'Type' is the kind reflecting 'GenericValue'
-- and will not have a Typeable constraint provided, so having this just distracts from the actual error
-- of not using 'TypeableValue'.
-- instance KindComparable Type Typeable where
--  testEqualityOnKind = eqT
-- Instead, a quick helper function to consume proxies:
eqTProxy :: forall s t. (Typeable s, Typeable t) => Proxy# s -> Proxy# t -> Maybe (s :~: t)
eqTProxy _ _ = eqT

class NoCon (a :: *)
instance NoCon a
instance TypeError (Text "Tokens for values reflected with 'GenericValue' are not comparable" :$$:
                    Text "Perhaps you wanted to use 'TypeableValue'?") => KindComparable Type where
  type KindEqualityCon Type = NoCon
  testEqualityOnKind = error "unreachable"
