module Choice where

open import Level

AxiomOfChoice : ∀ ℓ → Set (suc ℓ)
AxiomOfChoice ℓ = (A : Set ℓ) → .A → A
