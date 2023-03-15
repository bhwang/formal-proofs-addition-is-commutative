-- We need to hide a couple parts of Idris's Prelude, which is included by
-- default when running any Idris program.
%hide plus
%hide Nat

-- Defining the natural numbers
data Nat : Type where
  Z : Nat
  S : Nat -> Nat


-- Defining addition
plus : Nat -> Nat -> Nat
plus Z     m = m
plus (S k) m = S (plus k m)


-- Equality is built-in, but conceptually has the following definition:
-- data (=) : a -> b -> Type where
--   Refl : x = x


-- A couple of elementary lemmas about natural numbers.
total  -- Declares that the following function is not partial.- 
plusZeroRightNeutral : (n : Nat) -> plus n Z = n
plusZeroRightNeutral Z = Refl
plusZeroRightNeutral (S n) = rewrite plusZeroRightNeutral n in Refl

total
plusSuccRightSucc : (m, n : Nat) -> S (plus m n) = plus m (S n)
plusSuccRightSucc Z _ = Refl
plusSuccRightSucc (S m) n = rewrite plusSuccRightSucc m n in Refl


-- Our desired result
total  
plusCommutative : (m, n : Nat) -> plus m n = plus n m 
plusCommutative Z n = rewrite plusZeroRightNeutral n in Refl
plusCommutative (S m) n =
  rewrite plusCommutative m n in
    rewrite plusSuccRightSucc n m in
      Refl
