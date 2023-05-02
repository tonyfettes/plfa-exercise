module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; _+_; _*_; _∸_; _^_) renaming (suc to succ)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = refl

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (succ m) n p =
  begin
    (succ m + n) + p
  ≡⟨⟩
    succ ((m + n) + p)
  ≡⟨ cong succ (+-assoc m n p) ⟩
    succ (m + (n + p))
  ≡⟨⟩
    succ m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (succ m) =
  begin
    (succ m) + zero
  ≡⟨⟩
    succ (m + zero)
  ≡⟨ cong succ (+-identityʳ m) ⟩
    succ m
  ∎

+-succʳ : ∀ (m n : ℕ) → m + succ n ≡ succ (m + n)
+-succʳ zero n = refl
+-succʳ (succ m) n =
  begin
    (succ m) + (succ n)
  ≡⟨⟩
    succ (m + succ n)
  ≡⟨ cong succ (+-succʳ m n) ⟩
    succ (succ (m + n))
  ≡⟨⟩
    succ ((succ m) + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n =
  begin
    zero + n
  ≡⟨⟩
    n
  ≡⟨ sym (+-identityʳ n) ⟩
    n + zero
  ∎
+-comm (succ m) n =
  begin
    (succ m) + n
  ≡⟨⟩
    succ (m + n)
  ≡⟨ cong succ (+-comm m n) ⟩
    succ (n + m)
  ≡⟨ sym (+-succʳ n m) ⟩
    n + (succ m)
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q)  ⟩
    m + n + p + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    m + (n + p) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (succ m) n p rewrite +-assoc′ m n p = refl

+-succ′ : ∀ (m n : ℕ) → m + succ n ≡ succ (m + n)
+-succ′ zero n = refl
+-succ′ (succ m) n rewrite +-succ′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identityʳ n = refl
+-comm′ (succ m) n rewrite +-comm′ m n | +-succʳ n m = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (succ m) n p rewrite +-swap m n p | +-succ′ n (m + p) = refl

*-dist-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-dist-+ zero n p = refl
*-dist-+ (succ m) n p rewrite *-dist-+ m n p | +-assoc′ p (m * p) (n * p) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (succ m) n p rewrite *-dist-+ n (m * n) p | *-assoc m n p = refl

*-zeroʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (succ n) rewrite *-zeroʳ n = refl

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero = refl
*-identityʳ (succ n) rewrite *-identityʳ n = refl

*-succʳ : ∀ (m n : ℕ) → m * (succ n) ≡ m + (m * n)
*-succʳ zero n = refl
*-succʳ (succ m) n rewrite *-succʳ m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (succ m) n rewrite *-succʳ n m | *-comm m n = refl

∸-zeroˡ : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-zeroˡ zero = refl
∸-zeroˡ (succ n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero zero p = refl
∸-+-assoc zero (succ n) zero = refl
∸-+-assoc zero (succ n) (succ p) = refl
∸-+-assoc (succ m) zero p = refl
∸-+-assoc (succ m) (succ n) p rewrite ∸-+-assoc m n p = refl

^-distˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distˡ-+-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distˡ-+-* m (succ n) p rewrite ^-distˡ-+-* m n p | *-assoc m (m ^ n) (m ^ p)= refl

*-swap-inner : ∀ (m n p q : ℕ) → (m * n) * (p * q) ≡ (m * p) * (n * q)
*-swap-inner m n p q =
  begin
    (m * n) * (p * q)
  ≡⟨ *-assoc m n (p * q) ⟩
    m * (n * (p * q))
  ≡⟨ cong (_*_ m) (sym (*-assoc n p q)) ⟩
    m * (n * p * q)
  ≡⟨ cong (_*_ m) (cong (_* q) (*-comm n p)) ⟩
    m * (p * n * q)
  ≡⟨ cong (_*_ m) (*-assoc p n q) ⟩
    m * (p * (n * q))
  ≡⟨ sym (*-assoc m p (n * q)) ⟩
    (m * p) * (n * q)
  ∎
  --   *-assoc m n (p * q)
  -- | sym (*-assoc n p q)
  -- | *-comm n p
  -- | *-assoc p n q
  -- | sym (*-assoc m p (n * q)) = refl

^-distʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distʳ-* m n zero = refl
^-distʳ-* m n (succ p) rewrite ^-distʳ-* m n p | *-swap-inner m n (m ^ p) (n ^ p) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-zeroʳ n = refl
^-*-assoc m n (succ p) rewrite ^-*-assoc m n p | *-succʳ n p | sym (^-distˡ-+-* m n (n * p)) = refl

