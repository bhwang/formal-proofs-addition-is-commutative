module +-comm-no-imports where

-- Notions of equality and congrunece
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl  =  refl

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl  =  refl


-- Syntactic sugar for equational reasoning
infix  3 _∎
infixr 2 _≡⟨⟩_ step-≡ step-≡˘
infix  1 begin_

begin_ : ∀{A : Set} {x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : ∀ {A : Set} (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

step-≡ : ∀ {A : Set} (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_∎ _ = refl

syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z


-- Definition of natural numbers (following Peano axioms)
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


-- Definition of addition
_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)


-- Elementary lemmas
+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-identityʳ : (n : ℕ) → n + zero ≡ n
+-identityʳ zero = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)


-- Proof of the result
+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-identityʳ n)  -- Uses n + 0 ≡ n
+-comm (suc m) n = begin
  suc m + n   ≡⟨⟩
  suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩ -- Uses inductive hypothesis
  suc (n + m) ≡⟨ sym (+-suc n m) ⟩       -- Uses 1 + (n + m) ≡ n + (1 + m) 
  n + suc m   ∎ 
