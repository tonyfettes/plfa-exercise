module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym; trans)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ ; zero; _+_) renaming (suc to succ)
open import Data.Nat.Properties using (+-comm; +-identityʳ) renaming (+-suc to +-succ)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ (succ n) = succ (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m zero = +-comm zero m
  -- sym (+-identityʳ m)
  -- begin
  --   m +′ zero
  -- ≡⟨⟩
  --   zero + m
  -- ≡⟨ (+-comm zero m) ⟩
  --   m + zero
  -- ∎
same-app m (succ n) = trans (cong succ (same-app m n)) (sym (+-succ m n)) 
  -- begin
  --   m +′ (succ n)
  -- ≡⟨⟩
  --   succ (m +′ n)
  -- ≡⟨ cong succ (same-app m n) ⟩
  --   succ (m + n)
  -- ≡⟨ sym (+-succ m n) ⟩
  --   m + succ n
  -- ∎

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x) → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    into : A → B
    from : B → A
    from∘into : ∀ (x : A) → from (into x) ≡ x
    into∘from : ∀ (x : B) → into (from x) ≡ x

open _≃_

data _≃′_ (A B : Set) : Set where
  mk-≃′ : ∀ (into : A → B) →
         ∀ (from : B → A) →
         ∀ (from∘into : (∀ (x : A) → from (into x) ≡ x)) →
         ∀ (into∘from : (∀ (x : B) → into (from x) ≡ x)) →
         A ≃′ B

into′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
into′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘into′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (into′ A≃B x) ≡ x)
from∘into′ (mk-≃′ f g g∘f f∘g) = g∘f

into∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → into′ A≃B (from′ A≃B y) ≡ y)
into∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

id : ∀ {A : Set} (x : A) → A
id x = x

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { into = id
    ; from = id
    ; from∘into = λ x → refl
    ; into∘from = λ x → refl
    }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
  record
    { into = from A≃B
    ; from = into A≃B
    ; from∘into = into∘from A≃B
    ; into∘from = from∘into A≃B
    }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
  record
    { into = into B≃C ∘ into A≃B
    ; from = from A≃B ∘ from B≃C
    ; from∘into = λ x →
      begin
        from A≃B (from B≃C (into B≃C (into A≃B x)))
      ≡⟨ cong (from A≃B) (from∘into B≃C (into A≃B x)) ⟩
        from A≃B (into A≃B x)
      ≡⟨ from∘into A≃B x ⟩
        x
      ∎
    ; into∘from = λ x →
      begin
        into B≃C (into A≃B (from A≃B (from B≃C x)))
      ≡⟨ cong (into B≃C) (into∘from A≃B (from B≃C x)) ⟩
        into B≃C (from B≃C x)
      ≡⟨ (into∘from B≃C x) ⟩
        x
      ∎
    }

module ≃-Reasoning where
  infix 1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix 3 _≃-∎

  ≃-begin_ : ∀ {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    into : A → B
    from : B → A
    from∘into : ∀ (x : A) → from (into x) ≡ x

open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { into = λ x → x
    ; from = λ y → y
    ; from∘into = λ x → refl
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { into = λ x → into B≲C (into A≲B x)
    ; from = λ y → from A≲B (from B≲C y)
    ; from∘into = λ x →
      begin
        from A≲B (from B≲C (into B≲C (into A≲B x)))
      ≡⟨ cong (from A≲B) (from∘into B≲C (into A≲B x)) ⟩
         from A≲B (into A≲B x)
      ≡⟨ from∘into A≲B x ⟩
         x
      ∎
    }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (into A≲B ≡ from B≲A)
  → (from A≲B ≡ into B≲A)
  → A ≃ B
≲-antisym A≲B B≲A into≡from from≡into =
  record
    { into = into A≲B
    ; from = from A≲B
    ; from∘into = from∘into A≲B
    ; into∘from = λ x ->
      begin
        into A≲B (from A≲B x)
      ≡⟨ cong (into A≲B) (cong-app from≡into x) ⟩
        into A≲B (into B≲A x)
      ≡⟨ cong-app into≡from (into B≲A x) ⟩
        from B≲A (into B≲A x)
      ≡⟨ from∘into B≲A x ⟩
        x
      ∎
    }

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

≃-implies-≲ : ∀ {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B =
  record
    { into = into A≃B
    ; from = from A≃B
    ; from∘into = from∘into A≃B
    }

record _⇔_ (A B : Set) : Set where
  field
    into : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl =
  record
    { into = id
    ; from = id
    }

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym A⇔B =
  record
    { into = from A⇔B
    ; from = into A⇔B
    }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { into = into B⇔C ∘ into A⇔B
    ; from = from A⇔B ∘ from B⇔C
    }
