{-# LANGUAGE DataKinds, GADTs, TypeFamilies #-}
module AdditionCommutative where

-- Unary natural numbers, represented at the type level, in GADT syntax.
data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

-- Addition, also represented at the type level. 
-- (DataKinds is doing the heavy lifting in the background.)
type family (a :: Nat) + (b :: Nat) :: Nat where
  'Zero + n = n
  'Succ m + n = 'Succ (m + n)
  -- Quotes (') are used in the DataKinds extension to distinguish between 
  -- type-level constructors and value-level constructors of promoted types.

-- Type equality
data a :=: b where
  Refl :: a :=: a

-- We introduce singleton types which allows us to wrap Nat's and pattern
-- match on the given parameter.
data SNat (n :: Nat) where
  SZero :: SNat 'Zero
  SSucc :: SNat n -> SNat ('Succ n)


-- We can now prove commutativity of addition via our usual lemmas.

-- n + 0 = 0
rightIdentity :: SNat n -> (n + 'Zero) :=: n
rightIdentity SZero = Refl
rightIdentity (SSucc n') = case rightIdentity n' of Refl -> Refl

-- m + succ n = succ (m + n)
plusSucc :: SNat m -> SNat n -> (m + 'Succ n) :=: 'Succ (m + n)
plusSucc SZero _ = Refl
plusSucc (SSucc m') n = case plusSucc m' n of Refl -> Refl

-- m + n = n + m
additionCommutative :: SNat m -> SNat n -> (m + n) :=: (n + m)
additionCommutative SZero n = case rightIdentity n of Refl -> Refl
additionCommutative (SSucc m') n = 
  case (additionCommutative m' n, plusSucc n m') of (Refl, Refl) -> Refl
