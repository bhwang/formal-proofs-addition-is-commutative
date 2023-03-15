module +-comm where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- Proof of the result
+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-identityʳ n)  -- Uses n + 0 ≡ n
+-comm (suc m) n = begin
  suc m + n   ≡⟨⟩
  suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩ -- Uses inductive hypothesis
  suc (n + m) ≡⟨ sym (+-suc n m) ⟩       -- Uses 1 + (n + m) ≡ n + (1 + m) 
  n + suc m   ∎ 
