{-# OPTIONS --exact-split #-}
module plfa.Naturals where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

one : ℕ
one = succ zero

two : ℕ
two = succ one

three : ℕ
three = succ two

seven : ℕ
seven = succ (succ (succ (succ (succ (succ (succ zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

+-example-0 : 2 + 3 ≡ 5
+-example-0 = refl

+-example-1 : 3 + 4 ≡ 7
+-example-1 = refl

_*_ : ℕ → ℕ → ℕ
zero * m = zero
(succ n) * m = m + (n * m)

*-example-0 : 2 * 3 ≡ 6
*-example-0 = refl

*-example-1 : 3 * 4 ≡ 12
*-example-1 = refl

_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (succ n) = m * (m ^ n)

^-example-0 : 3 ^ 4 ≡ 81
^-example-0 = refl

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ (succ n) = zero
(succ m) ∸ (succ n) = m ∸ n

∸-example-0 : 3 ∸ 2 ≡ 1
∸-example-0 = refl

∸-example-1 : 2 ∸ 3 ≡ 0
∸-example-1 = refl

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

_++ : Bin → Bin
⟨⟩ ++ = ⟨⟩ I
(n O) ++ = n I
(n I) ++ = (n ++) O

++-example-0 : (⟨⟩ I O I I) ++ ≡ ⟨⟩ I I O O
++-example-0 = refl

_into : ℕ → Bin
zero into = ⟨⟩
(succ n) into = (n into) ++

into-example-0 : 11 into ≡ ⟨⟩ I O I I
into-example-0 = refl

from : Bin → ℕ
from ⟨⟩ = 0
from (n O) = (from n) * 2
from (n I) = (from n) * 2 + 1

from-example-0 : from (⟨⟩ I O I I) ≡ 11
from-example-0 = refl
