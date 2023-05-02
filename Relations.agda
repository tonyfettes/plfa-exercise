module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; _+_; _*_) renaming (suc to succ)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm) renaming (+-suc to +-succ)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → succ m ≤ succ n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → succ m ≤ succ n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {succ n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong succ (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

data Total′ : ℕ → ℕ → Set where
  forward′ : ∀ {m n : ℕ} → m ≤ n → Total′ m n
  flipped′ : ∀ {m n : ℕ} → n ≤ m → Total′ m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (succ m) zero = flipped z≤n
≤-total (succ m) (succ n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (succ n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (succ n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < succ n
  s<s : ∀ {m n : ℕ} → m < n → succ m < succ n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

infix 4 _>_

data _>_ : ℕ → ℕ → Set where
  s>z : ∀ {n : ℕ} → succ n > zero
  s>s : ∀ {m n : ℕ} → m > n → succ m > succ n

data Trichotomy (m n : ℕ) : Set where
  less : m < n → Trichotomy m n
  equal : m ≡ n → Trichotomy m n
  greater : m > n → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = equal refl
trichotomy zero (succ n) = less z<s
trichotomy (succ m) zero = greater s>z
trichotomy (succ m) (succ n) with trichotomy m n
... | less m<n = less (s<s m<n)
... | equal m≡n = equal (cong succ m≡n)
... | greater m>n = greater (s>s m>n)

+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (succ n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-succ-< : ∀ {m n : ℕ} → m ≤ n → m < (succ n)
≤-succ-< z≤n = z<s
≤-succ-< (s≤s m≤n) = s<s (≤-succ-< m≤n)

≤-iff-< : ∀ (m n : ℕ) → (succ m) ≤ n → m < n
≤-iff-< m (succ p) (s≤s m≤p) = ≤-succ-< m≤p

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  succ : ∀ {n : ℕ} → odd n → even (succ n)

data odd where
  succ : ∀ {n : ℕ} → even n → odd (succ n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)
e+e≡e zero en = en
e+e≡e (succ om) en = succ (o+e≡o om en)
o+e≡o (succ em) en = succ (e+e≡e em en)

e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)
o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
e+o≡o zero on = on
e+o≡o (succ om) on = succ (o+o≡e om on)
o+o≡e (succ em) on = succ (e+o≡o em on)
