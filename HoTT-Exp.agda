{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-Exp where

open import Universes public



-- UNIT TYPE

data 𝟙 : 𝓤 ̇ where
  * : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A * → ( x : 𝟙) → A x
𝟙-induction A a * = a 
