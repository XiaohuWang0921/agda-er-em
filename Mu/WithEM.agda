open import Relation.Unary hiding (Stable)
open import Data.Nat.Base
open import Data.Product.Base
open import Relation.Nullary

module Mu.WithEM {ℓ} {P : Pred ℕ ℓ} (@0 ∃P? : Dec (∃[ n ] P n)) where

open import Mu
open import Relation.Nullary.Decidable

-- This formulation of Markov's Principle is found e.g. in
-- ⟪Varieties of Constructive Mathematics⟫ by Bridges and Richman,
-- Chapter 7, Section 2, Page 137.
markov : Decidable P → Stable (∃[ n ] P n)
markov P? ¬¬∃p = μ P? (decidable-stable ∃P? ¬¬∃p)
