module plfa.Binary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; _+_; _*_; _∸_; _^_) renaming (suc to succ)
open import Data.Nat.Properties using (+-identityʳ) renaming (+-suc to +-succ)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

incr : Bin → Bin
incr ⟨⟩ = ⟨⟩ I
incr (n O) = n I
incr (n I) = (incr n) O

incr-example₀ : incr (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
incr-example₀ = refl

_into : ℕ → Bin
zero into = ⟨⟩
(succ n) into = incr (n into)

into-example₀ : 11 into ≡ ⟨⟩ I O I I
into-example₀ = refl

-- from : Bin → ℕ
-- from ⟨⟩ = 0
-- from (n O) = (from n) * 2
-- from (n I) = (from n) * 2 + 1

-- from-example₀ : from (⟨⟩ I O I I) ≡ 11
-- from-example₀ = refl

-- incr-succ : ∀ (b : Bin) → from (incr b) ≡ succ (from b)
-- incr-succ ⟨⟩ = refl
-- incr-succ (b O) rewrite +-succ ((from b) * 2) zero | +-identityʳ ((from b) * 2) = refl
-- incr-succ (b I) rewrite incr-succ b | +-succ ((from b) * 2) zero | +-identityʳ ((from b) * 2) = refl

-- into-from : ∀ (n : ℕ) → from (n into) ≡ n
-- into-from zero = refl
-- into-from (succ n) rewrite incr-succ (n into) | into-from n = refl

-- from-into : ∀ (b : Bin) → (from b) into ≡ b
-- from-into b H = ?

data ℙ : Set where
  l : ℙ
  _O : ℙ → ℙ
  _I : ℙ → ℙ

data 𝔹 : Set where
  o : 𝔹
  i : ℙ → 𝔹

_++ₚ : ℙ → ℙ
l ++ₚ = l O
(p O) ++ₚ = p I
(p I) ++ₚ = (p ++ₚ) O

_++ : 𝔹 → 𝔹
o ++ = i l
i b ++ = i (b ++ₚ)

_to-𝔹 : ∀ (n : ℕ) → 𝔹
zero to-𝔹 = o
(succ n) to-𝔹 = (n to-𝔹) ++

_to-ℕ : ∀ (b : 𝔹) → ℕ
_to-ℕ o = 0
_to-ℕ (i l) = 1
_to-ℕ (i (p O)) = (_to-ℕ (i p)) * 2
_to-ℕ (i (p I)) = (_to-ℕ (i p)) * 2 + 1

++-succ : ∀ (b : 𝔹) → (b ++) to-ℕ ≡ succ (b to-ℕ)
++-succ o = refl
++-succ (i l) = refl
++-succ (i (p O)) rewrite +-succ ((i p to-ℕ) * 2) zero | +-identityʳ ((i p to-ℕ) * 2) = refl
++-succ (i (p I)) rewrite ++-succ (i p) | +-succ ((i p to-ℕ) * 2) zero | +-identityʳ ((i p to-ℕ) * 2) = refl

ℕ-iso-𝔹 : ∀ (n : ℕ) → n to-𝔹 to-ℕ ≡ n
ℕ-iso-𝔹 zero = refl
ℕ-iso-𝔹 (succ n) rewrite ++-succ (n to-𝔹) | ℕ-iso-𝔹 n = refl

𝔹-iso-ℕ : ∀ (b : 𝔹) → b to-ℕ to-𝔹 ≡ b
𝔹-iso-ℕ o = refl
𝔹-iso-ℕ (i l) = refl
𝔹-iso-ℕ (i (p O)) = {!!}
𝔹-iso-ℕ (i (p I)) = {!!}
