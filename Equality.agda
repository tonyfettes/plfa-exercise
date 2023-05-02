module plfa.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} {f : A → B → C} {u x : A} {v y : B} → u ≡ x → v ≡ y → f u v ≡ f x y
cong₂ refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {a : Set} {x y : a} (p : a → Set) → x ≡ y → p x → p y
subst p refl px = px

module ≡-Reasoning {A : Set} where
  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ {_R_ : A → A → Set} (x : A) {y : A} → x R y → x R y
  x ≡⟨⟩ xRy = xRy

  _≡⟨_⟩_ : ∀ {_R_ : A → A → Set} (x : A) {y z : A} → x ≡ y → y R z → x R z
  x ≡⟨ refl ⟩ yRz = yRz

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero + n = n
(succ m) + n = succ (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-succ : ∀ (m n : ℕ) → m + succ n ≡ succ (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-identity n)
+-comm (succ m) n = trans (cong succ (+-comm m n)) (sym (+-succ n m))

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → succ m ≤ succ n

infix 4 _≤_

postulate
  ≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

≤-from-≡ : ∀ {m n : ℕ} → m ≡ n → m ≤ n
≤-from-≡ {zero} m≡n = z≤n
≤-from-≡ {succ m} {succ n} m≡n = s≤s (≤-from-≡ (cong pred m≡n))

module ≤-Reasoning where
  infix 1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _≤-∎

  ≤-begin_ : ∀ {m n : ℕ} → m ≤ n → m ≤ n
  ≤-begin m≤n = m≤n

  _≤⟨⟩_ : ∀ (m : ℕ) {n : ℕ} → m ≤ n → m ≤ n
  m ≤⟨⟩ m≤n = m≤n

  _≤⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
  m ≤⟨ m≤n ⟩ n≤p = ≤-trans m≤n n≤p

  _≤-∎ : ∀ (n : ℕ) → n ≤ n
  zero ≤-∎ = z≤n
  succ n ≤-∎ = s≤s (n ≤-∎)

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n : ℕ) {p q : ℕ} → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero {p} {q} p≤q =
  ≤-begin
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  ≤-∎
+-monoʳ-≤ (succ n) {p} {q} p≤q =
  ≤-begin
    (succ n) + p
  ≤⟨⟩
    succ (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p≤q) ⟩
    succ (n + q)
  ≤⟨⟩
    (succ n) + q
  ≤-∎

+-monoˡ-≤ : ∀ {p q : ℕ} → p ≤ q → (n : ℕ) → p + n ≤ q + n
+-monoˡ-≤ {p} {q} p≤q zero =
  ≤-begin
    p + zero
  ≤⟨ ≤-from-≡ (+-identity p) ⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨ ≤-from-≡ (sym (+-identity q)) ⟩
    q + zero
  ≤-∎
+-monoˡ-≤ {p} {q} p≤q (succ n) =
  ≤-begin
    p + (succ n)
  ≤⟨ ≤-from-≡ (+-succ p n) ⟩
    succ (p + n)
  ≤⟨ s≤s (+-monoˡ-≤ p≤q n) ⟩
    succ (q + n)
  ≤⟨ ≤-from-≡ (sym (+-succ q n) ) ⟩
    q + (succ n)
  ≤-∎

+-mono-≤ : ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ {m} {n} {p} {q} m≤n p≤q =
  ≤-begin
    m + p
  ≤⟨ +-monoˡ-≤ m≤n p ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p≤q ⟩
    n + q
  ≤-∎

data even : ℕ → Set
data oddy : ℕ → Set

data even where

  even-zero : even zero

  even-succ : ∀ {n : ℕ}
    → oddy n
      ------------
    → even (succ n)

data oddy where
  oddy-succ : ∀ {n : ℕ}
    → even n
      -----------
    → oddy (succ n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ {m n : ℕ} → even (m + n) → even (n + m)
even-comm {m} {n} ev rewrite +-comm m n = ev

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (succ m) n rewrite +-succ n m | +-comm′ m n = refl

even-comm′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′ m n ev with
      .(m + n) | +-comm m n
... | .(n + m) | refl = ev

even-comm′′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′′ m n ev = subst even (+-comm m n) ev

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

≐-refl : ∀ {A : Set} {x : A} → x ≐ x
≐-refl P Px = Px

≐-trans : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
≐-trans x≐y y≐z P Px = y≐z P (x≐y P Px)

≐-sym : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
≐-sym {A} {x} {y} x≐y P = x≐y Q (≐-refl P)
  where
    Q : A → Set
    Q z = P z → P x

≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P Px = subst P x≡y Px

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = x≐y Q refl
  where
    Q : A → Set
    Q z = x ≡ z

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsucc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡′ y → y ≡′ x
sym′ refl′ = refl′

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsucc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)
