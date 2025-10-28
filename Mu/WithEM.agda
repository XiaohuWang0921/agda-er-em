open import Relation.Unary hiding (Stable)
open import Data.Nat.Base
open import Data.Product.Base
open import Relation.Nullary

module Mu.WithEM {ℓ} {P : Pred ℕ ℓ} (@0 ∃P? : Dec (∃[ n ] P n)) where

open import Mu
open import Relation.Nullary.Decidable

markov : Decidable P → Stable (∃[ n ] P n)
markov P? ¬¬∃p = μ P? (decidable-stable ∃P? ¬¬∃p)
