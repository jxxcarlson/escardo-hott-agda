{-# OPTIONS --without-K --exact-split --safe #-}

module HOUT where

open import Universes public

variable

  𝓤 : Universe

-- UNIT TYPE

data 𝟙 : 𝓤 ̇ where
  * : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A * → ( x : 𝟙) → A x
𝟙-induction A a * = a 

𝟙-recursion : (B : 𝓤 ̇) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙' : (X : 𝓤 ̇) → X → 𝟙
!𝟙' X x = *

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = *


 
-- EMPTY TYPE

data 𝟘 : 𝓤 ̇ where

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

