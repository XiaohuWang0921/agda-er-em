module Mu.SplitEpi where

open import Mu.Choice
open import Data.Nat.Base
open import Data.Product.Base
open import Function.Base
open import Relation.Binary.Bundles

rightInv : ∀ {a ℓ} {A : DecSetoid a ℓ} (open DecSetoid A) (f : ℕ → Carrier) → @0 (∀ x → ∃[ n ] f n ≈ x) → Σ[ g ∈ (Carrier → ℕ) ] ∀ x → f (g x) ≈ x
rightInv {A = A} f = let open DecSetoid A in choice (flip (_≟_ ∘ f))
