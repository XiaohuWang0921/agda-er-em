open import Relation.Nullary
open import SemiDec
open import Data.Product.Base

module SemiDec.WithEM {ℓ} {P : Set ℓ} (@0 P? : Dec P)
  ((M , iffM) : SemiDec P) ((N , iffN) : SemiDec (¬ P)) where

open import Mu
open import Relation.Nullary.Decidable
open import Data.Bool.Base
open import Relation.Binary.Morphism.Bundles
open import Data.Sum.Base hiding (map; map₁; map₂)
open import Data.Nat.Base
open import Function.Bundles

open PosetHomomorphism
open Equivalence

@0 ∃-∨ : ∃[ n ] (T (⟦ M ⟧ n) ⊎ T (⟦ N ⟧ n))
∃-∨ with toSum P?
... | inj₁ p = map₂ inj₁ (iffM .from p)
... | inj₂ ¬p = map₂ inj₂ (iffN .from ¬p)


