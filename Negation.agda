module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import Data.Nat using (ℕ; zero; suc; pred)
open import plfa.Relations using (_<_; s<s; _>_; <-trans; s>s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import plfa.Isomorphism using (_≃_; extensionality; _∘_)

-- reductio ad absurdum
¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality λ()

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x x)

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s n<n) = <-irreflexive n<n

<-trichotomy-≡ : ∀ {m n : ℕ} → m < n → ¬ (m ≡ n)
<-trichotomy-≡ (s<s m<n) refl = <-trichotomy-≡ m<n refl

_≯_ : ∀ (m n : ℕ) → Set
m ≯ n = ¬ (m > n)

<-trichotomy-> : ∀ {m n : ℕ} → m < n → ¬ (m > n)
<-trichotomy-> (s<s m<n) (s>s m>n) = <-trichotomy-> m<n m>n

-- De Morgan's Law
⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { into = λ ¬w → (¬w ∘ inj₁ , ¬w ∘ inj₂)
    ; from = λ { (¬a , ¬b) → λ { (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b }}
    ; from∘into = λ ¬w → extensionality λ { (inj₁ a) → refl ; (inj₂ b) → refl }
    ; into∘from = λ { (¬a , ¬b) → refl }
    }

×-dual-⊎ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎ (inj₁ ¬A) (A , B) = ¬A A
×-dual-⊎ (inj₂ ¬B) (A , B) = ¬B B

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ (λ x → k (inj₁ x)))

-- em-implies-dne : ∀ {A : Set} → A ⊎ ¬ A → ∀ (B : Set) → ¬ ¬ A → A
-- em-implies-dne (inj₁ A) ¬¬A = A
-- em-implies-dne (inj₂ ¬A) ¬¬A = ⊥-elim (¬¬A ¬A)

-- dne-implies-peirce : ∀ {A B : Set} → (¬ ¬ A → A) → ((A → B) → A) → A
-- dne-implies-peirce ¬¬A→A ABA = ⊥-elim {!!}

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-Stable : ∀ (A : Set) → Stable (¬ A)
¬-Stable A ¬¬¬A = ¬¬¬-elim ¬¬¬A

×-Stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-Stable ¬¬A→A ¬¬B→B ¬¬A×B = ¬¬A→A (λ ¬A → ¬¬A×B λ (A , B) → ¬A A)
                             , ¬¬B→B (λ ¬B → ¬¬A×B (λ (A , B) → ¬B B))
