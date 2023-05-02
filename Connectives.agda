module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; _≲_; extensionality; _⇔_; ≃-trans)
open plfa.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

projₗ : ∀ {A B : Set} → A × B → A
projₗ ⟨ x , y ⟩ = x

projᵣ : ∀ {A B : Set} → A × B → B
projᵣ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ projₗ w , projᵣ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    projₗ′ : A
    projᵣ′ : B

open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ projₗ′ w , projᵣ′ w ⟩′ ≡ w
η-×′ w = refl

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { into = λ { ⟨ l , r ⟩ → ⟨ r , l ⟩ }
    ; from = λ { ⟨ l , r ⟩ → ⟨ r , l ⟩ }
    ; from∘into = λ { ⟨ l , r ⟩ → refl }
    ; into∘from = λ { ⟨ l , r ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { into = λ { ⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩ }
    ; from = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩ }
    ; from∘into = λ { ⟨ ⟨ a , b ⟩ , c ⟩ → refl }
    ; into∘from = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → refl }
    }

open _⇔_

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ (A → B) × (B → A)
⇔≃× =
  record
    { into = λ A⇔B → ⟨ into A⇔B , from A⇔B ⟩
    ; from = λ { ⟨ A→B , B→A ⟩ → record { into = A→B ; from = B→A } }
    ; from∘into = λ A⇔B → refl
    ; into∘from = λ { ⟨ A→B , B→A ⟩ → refl }
    }

data ⊤ : Set where
  top : ⊤

η-⊤ : ∀ (w : ⊤) → top ≡ w
η-⊤ top = refl

record ⊤′ : Set where
  constructor top′

η-⊤′ : ∀ (w : ⊤′) → top′ ≡ w
η-⊤′ w = refl

truth′ : ⊤′
truth′ = _

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { into = λ { ⟨ top , a ⟩ → a }
    ; from = λ a → ⟨ top , a ⟩
    ; from∘into = λ { ⟨ top , a ⟩ → refl }
    ; into∘from = λ a → refl
    }

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ = ≃-trans ×-comm ⊤-identityˡ

data _⊎_ (A B : Set) : Set where
  injₗ : A → A ⊎ B
  injᵣ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B) → C
case-⊎ A→C B→C (injₗ l) = A→C l
case-⊎ A→C B→C (injᵣ r) = B→C r

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ injₗ injᵣ w ≡ w
η-⊎ (injₗ l) = refl
η-⊎ (injᵣ r) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ injₗ) (h ∘ injᵣ) w ≡ h w
uniq-⊎ h (injₗ l) = refl
uniq-⊎ h (injᵣ r) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { into = λ A⊎B → case-⊎ injᵣ injₗ A⊎B
    ; from = λ B⊎A → case-⊎ injᵣ injₗ B⊎A
    ; from∘into = λ
      { (injₗ a) → refl
      ; (injᵣ b) → refl
      }
    ; into∘from = λ
      { (injₗ b) → refl
      ; (injᵣ a) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { into = λ
      { (injₗ (injₗ a)) → injₗ a
      ; (injₗ (injᵣ b)) → injᵣ (injₗ b)
      ; (injᵣ c) → injᵣ (injᵣ c) }
    ; from = λ
      { (injₗ a) → injₗ (injₗ a)
      ; (injᵣ (injₗ b)) → injₗ (injᵣ b)
      ; (injᵣ (injᵣ c)) → injᵣ c
      }
    ; from∘into = λ
      { (injₗ (injₗ a)) → refl
      ; (injₗ (injᵣ b)) → refl
      ; (injᵣ c) → refl
      }
    ; into∘from = λ
      { (injₗ a) → refl
      ; (injᵣ (injₗ b)) → refl
      ; (injᵣ (injᵣ c)) → refl
      }
    }

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { into = λ { (injᵣ a) → a }
    ; from = injᵣ
    ; from∘into = λ { (injᵣ a) → refl }
    ; into∘from = λ { a → refl }
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ = ≃-trans ⊎-comm ⊥-identityˡ

-- modus ponens
→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ ((A × B) → C)
currying =
  record
    { into = λ { f ⟨ a , b ⟩ → f a b }
    ; from = λ { f a b → f ⟨ a , b ⟩ }
    ; from∘into = λ f → refl
    ; into∘from = λ { f → extensionality λ { ⟨ a , b ⟩ → refl } }
    }

→-dist-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-dist-⊎ =
  record
    { into = λ { f → ⟨ f ∘ injₗ , f ∘ injᵣ ⟩ }
    ; from = λ { ⟨ f , g ⟩ → λ { (injₗ a) → f a ; (injᵣ b) → g b } }
    ; from∘into = λ { f → extensionality λ { (injₗ x) → refl ; (injᵣ x) → refl } }
    ; into∘from = λ { ⟨ f , g ⟩ → refl }
    }

→-dist-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-dist-× =
  record
    { into = λ { f → ⟨ projₗ ∘ f , projᵣ ∘ f ⟩ }
    ; from = λ { ⟨ f , g ⟩ → λ a → ⟨ f a , g a ⟩ }
    ; from∘into = λ f → extensionality λ { a → η-× (f a) }
    ; into∘from = λ { ⟨ f , g ⟩ → refl }
    }

×-dist-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-dist-⊎ =
  record
    { into = λ
      { ⟨ injₗ a , c ⟩ → injₗ ⟨ a , c ⟩
      ; ⟨ injᵣ b , c ⟩ → injᵣ ⟨ b , c ⟩
      }
    ; from = λ
      { (injₗ ⟨ a , c ⟩) → ⟨ injₗ a , c ⟩
      ; (injᵣ ⟨ b , c ⟩) → ⟨ injᵣ b , c ⟩
      }
    ; from∘into = λ
      { ⟨ injₗ x , c ⟩ → refl
      ; ⟨ injᵣ x , c ⟩ → refl
      }
    ; into∘from = λ
      { (injₗ ⟨ a , c ⟩) → refl
      ; (injᵣ ⟨ b , c ⟩) → refl }
    }

⊎-dist-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-dist-× =
  record
    { into = λ
      { (injₗ ⟨ a , b ⟩) → ⟨ injₗ a , injₗ b ⟩
      ; (injᵣ c) → ⟨ injᵣ c , injᵣ c ⟩
      }
    ; from = λ
      { ⟨ injₗ a , injₗ b ⟩ → injₗ ⟨ a , b ⟩
      ; ⟨ injₗ a , injᵣ c ⟩ → injᵣ c
      ; ⟨ injᵣ c , g ⟩ → injᵣ c
      }
    ; from∘into = λ
      { (injₗ ⟨ a , b ⟩) → refl
      ; (injᵣ c) → refl
      }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ injₗ a , c ⟩ = injₗ a
⊎-weak-× ⟨ injᵣ b , c ⟩ = injᵣ ⟨ b , c ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (injₗ ⟨ a , b ⟩) = ⟨ injₗ a , injₗ b ⟩
⊎×-implies-×⊎ (injᵣ ⟨ c , d ⟩) = ⟨ injᵣ c , injᵣ d ⟩
