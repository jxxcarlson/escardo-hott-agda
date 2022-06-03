{-# OPTIONS --without-K --exact-split --safe #-}

module Nat where

open import Universes public

variable
  𝓤 𝓥 𝓦 𝓣 : Universe


-- THE EMPTY TYPE

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤 ̇) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘


-- THE UNIT TYPE

data 𝟙 : 𝓤₀ ̇ where
  * : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A * → (x : 𝟙) → A x
𝟙-induction A a * = a


𝟙-recursion : (B : 𝓤 ̇) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙' : (X : 𝓤 ̇) → X → 𝟙
!𝟙' X x = *

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = *


-- Identity types

data Id {𝓤} (X : 𝓤 ̇) : X → X → 𝓤 ̇ where
  refl : (x : X) → Id X x x

_≡_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≡ y = Id _ x y

sym : {A : 𝓤 ̇} { x y : A } → x ≡ y → y ≡ x
sym (refl x) = refl x

trans : { A :  𝓤 ̇} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl x) (refl x) = refl x

cong : {A B :  𝓤 ̇ } {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f (refl x) = (refl (f x))

-- EQUATIONAL REASONING

begin_ : { A : 𝓤 ̇} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : { A : 𝓤 ̇} → (x : A) → x ≡ x
x end = refl x

_=⟨_⟩_ : { A : 𝓤 ̇ } → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : 𝓤 ̇} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl x ⟩ q

infix 1  begin_
infix 3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_




data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}


_+_ _×_ : ℕ →  ℕ →  ℕ

x + 0      = x
x + succ y = succ (x + y)

x × 0      = 0
x × succ y = x + x × y


infixl 20 _+_
infixl 21 _×_

_-_ : ℕ → ℕ → ℕ
a - 0 = 0
0 - succ n = 0
succ m - succ n = m - n

infixl 21 _-_

_^_ : ℕ → ℕ → ℕ
a ^ 0 = 1
a ^ (succ n) = a × (a ^ n)


is-even : ℕ → 𝓤₀ ̇
is-even 0 = 𝟙
is-even (succ 0) = 𝟘
is-even (succ (succ n)) = is-even n


double : ℕ → ℕ
double 0 = 0
double (succ n) = succ (succ( double n))

double-is-even : (n : ℕ) → is-even(double n) ≡ 𝟙
double-is-even 0 = refl 𝟙
-- double-is-even (succ n) = 



