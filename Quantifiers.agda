module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-suc; +-identityʳ; +-comm)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.Isomorphism using (_≃_; extensionality; ∀-extensionality)
open import Function using (_∘_)

open import plfa.Relations using (even; odd)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
  → B M
∀-elim L M = L M

∀-dist-× : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-dist-× =
  record
    { into = λ ∀× → ⟨ proj₁ ∘ ∀× , proj₂ ∘ ∀× ⟩
    ; from = λ { ⟨ fb , fc ⟩ a → ⟨ fb a , fc a ⟩ }
    ; from∘into = λ ∀× → refl
    ; into∘from = λ { ⟨ fb , fc ⟩ → refl }
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
  → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ A→B) = λ x → inj₁ (A→B x)
⊎∀-implies-∀⊎ (inj₂ A→C) = λ x → inj₂ (A→C x)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

tri-∀-× : ∀ {B : Tri → Set}
  → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
tri-∀-× =
  record
    { into = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
    ; from = λ { ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ { aa → Baa ; bb → Bbb ; cc → Bcc } }
    ; from∘into = λ f → ∀-extensionality λ { aa → refl ; bb → refl ; cc → refl }
    ; into∘from = λ { ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → refl }
    }

data ∑ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → ∑ A B

∑-syntax = ∑
infix 2 ∑-syntax
syntax ∑-syntax A (λ x → B) = ∑[ x ∈ A ] B

record ∑′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = ∑ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim :  ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  → C
∃-elim f ⟨ a , Ba ⟩ = f a Ba

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { into = ∃-elim
    ; from = λ ∃xBx→C x Bx → ∃xBx→C ⟨ x , Bx ⟩
    ; from∘into = λ f → refl
    ; into∘from = λ ∃xBx→C → extensionality λ { ⟨ a , Ba ⟩ → refl }
    }

∃-dist-⊎ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-dist-⊎ =
  record
    { into = λ
      { ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
      ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩
      }
    ; from = λ
      { (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
      ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩
      }
    ; from∘into = λ
      { ⟨ x , inj₁ x₁ ⟩ → refl
      ; ⟨ x , inj₂ y ⟩ → refl
      }
    ; into∘from = λ
      { (inj₁ ⟨ x , Bx ⟩) → refl
      ; (inj₂ ⟨ x , Cx ⟩) → refl
      }
    }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩

tri-∃-⊎ : ∀ {B : Tri → Set}
  → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
tri-∃-⊎ =
  record
    { into = λ
      { ⟨ aa , Baa ⟩ → inj₁ Baa
      ; ⟨ bb , Bbb ⟩ → inj₂ (inj₁ Bbb)
      ; ⟨ cc , Bcc ⟩ → inj₂ (inj₂ Bcc)
      }
    ; from = λ
      { (inj₁ Baa) → ⟨ aa , Baa ⟩
      ; (inj₂ (inj₁ Bbb)) → ⟨ bb , Bbb ⟩
      ; (inj₂ (inj₂ Bcc)) → ⟨ cc , Bcc ⟩
      }
    ; from∘into = λ
      { ⟨ aa , Baa ⟩ → refl
      ; ⟨ bb , Bbb ⟩ → refl
      ; ⟨ cc , Bcc ⟩ → refl
      }
    ; into∘from = λ
      { (inj₁ Baa) → refl
      ; (inj₂ (inj₁ Bbb)) → refl
      ; (inj₂ (inj₂ Bcc)) → refl
      }
    }

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (m * 2 ≡ n)
odd-∃ : ∀ {n : ℕ} → odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even.zero = ⟨ zero , refl ⟩
even-∃ (even.succ o) with odd-∃ o
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd.succ e) with even-∃ e
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (m * 2 ≡ n) → even n
∃-odd : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) → odd n

∃-even ⟨ zero , refl ⟩ = even.zero
∃-even ⟨ suc m , refl ⟩ = even.succ (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = odd.succ (∃-even ⟨ m , refl ⟩)

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (2 * m ≡ n) → even n
∃-odd′ : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd n

+-congˡ : ∀ {m n : ℕ} (p : ℕ) → m ≡ n → p + m ≡ p + n
+-congˡ p m≡n = cong (_+_ p) m≡n
+-unit : ∀ (n : ℕ) → n + 1 ≡ suc n
+-unit n = +-comm n 1

∃-even′ ⟨ zero , refl ⟩ = even.zero
∃-even′ ⟨ suc m , refl ⟩ =
  even.succ (∃-odd′ ⟨ m , help ⟩)
  where
    help : ∀ {m : ℕ} → m + (m + zero) + 1 ≡ m + suc (m + zero)
    help {m} =
      begin
        (m + (m + zero)) + 1
      ≡⟨ +-assoc m (m + zero) 1 ⟩
        m + ((m + zero) + 1)
      ≡⟨ +-congˡ m (+-unit (m + zero)) ⟩
        m + suc (m + zero)
      ∎

∃-odd′ ⟨ m , refl ⟩ = subst odd help (odd.succ (∃-even′ {!!}))
  where
    postulate
      help : ∀ {m : ℕ} → suc (2 * m) ≡ m + (m + zero) + 1
