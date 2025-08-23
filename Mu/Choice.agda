module Mu.Choice where

open import Mu
open import Relation.Binary
open import Data.Nat.Base
open import Data.Product.Base

choice : ∀ {a ℓ} {A : Set a} {R : REL A ℕ ℓ} → Decidable R → @0 (∀ x → ∃[ n ] R x n) → Σ[ f ∈ (A → ℕ) ] ∀ x → R x (f x)
choice R? F = (λ x → μ (R? x) (F x) .proj₁) , (λ x → μ (R? x) (F x) .proj₂)
