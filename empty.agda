-- EMPTY TYPE

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤₀ ̇) → (x : 𝟘)  → A x  
𝟘-induction A ()

𝟘-recursion : ( A : 𝓤₀ ̇ ) → 𝟘 → A 
𝟘-recursion A a = 𝟘-induction (λ _ → A) a 

!𝟘 : (A :  𝓤₀ ̇ ) → 𝟘 → A 
!𝟘 = 𝟘-recursion

is-empty : 𝓤₀ ̇  → 𝓤₀ ̇ 
is-empty X = X → 𝟘

¬ : 𝓤₀ ̇ → 𝓤₀ ̇ 
¬ X = X → 𝟘
