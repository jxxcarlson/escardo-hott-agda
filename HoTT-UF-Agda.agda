{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-Agda where

open import Universes public

variable
  𝓤 : Universe

-- UNIT TYPE

data 𝟙 : 𝓤₀ ̇ where
  * : 𝟙

--𝟙-induction : (A : 𝟙 → 𝓤₀ ̇) → A * → ( x : 𝟙) → A x
𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A * → ( x : 𝟙) → A x
𝟙-induction A a * = a 

𝟙-recursion : (B : 𝓤 ̇) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙' : (X : 𝓤 ̇) → X → 𝟙
!𝟙' X x = *

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = *


 
-- EMPTY TYPE

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤 ̇) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : ( A : 𝓤 ̇) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : 𝓤 ̇) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ →  𝓤 ̇
¬ X = X → 𝟘

-- NATURAL NUMBERS

data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 ̇) → A 0 → ((n : ℕ) → A n → A (succ n)) → (n : ℕ) → A n
ℕ-induction A a₀ f = h
  where
    h : (n : ℕ) → A n
    h 0        = a₀
    h (succ n) = f n (h n)

-- ℕ-induction is a dependently typed version of ℕ-recursion:

ℕ-recursion : ( X : 𝓤 ̇) → X → (ℕ → X → X) → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ -> X)


ℕ-iteration : (X : 𝓤 ̇) → X → (X → X) → (ℕ → X)
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

module Arithmetic where

  _+_ : ℕ →  ℕ →  ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  infixl 20 _+_

