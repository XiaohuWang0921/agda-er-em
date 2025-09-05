open import Relation.Nullary
open import SemiDec
open import Data.Product.Base

module SemiDec.WithEM {ℓ} {P : Set ℓ}
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

dec⇒∃T⊎T : Dec P → ∃[ n ] (T (⟦ M ⟧ n) ⊎ T (⟦ N ⟧ n))
dec⇒∃T⊎T (yes p) = map₂ inj₁ (iffM .from p)
dec⇒∃T⊎T (no ¬p) = map₂ inj₂ (iffN .from ¬p)

erDec⇒dec : @0 Dec P → Dec P
erDec⇒dec P? with μ (λ n → T? (⟦ M ⟧ n) ⊎-dec T? (⟦ N ⟧ n)) (dec⇒∃T⊎T P?)
... | n , inj₁ T⟦M⟧n = yes (iffM .to (n , T⟦M⟧n))
... | n , inj₂ T⟦N⟧n = no (iffN .to (n , T⟦N⟧n))

