open import Relation.Nullary

module SemiDec.WithEM {ℓ} {P : Set ℓ} (@0 P? : Dec P) where

open import Mu
open import Relation.Nullary.Decidable
open import Data.Bool.Base
open import Relation.Binary.Morphism.Bundles
open import Data.Sum.Base hiding (map; map₁; map₂)
open import Data.Nat.Base
open import Function.Bundles
open import Function.Base
open import Data.Empty
open import Data.Product.Base
open import SemiDec

open PosetHomomorphism
open Equivalence

merge : SemiDec P → SemiDec (¬ P) → Dec P
merge (M , iffM) (N , iffN) with μ (λ n → T? (⟦ M ⟧ n) ⊎-dec T? (⟦ N ⟧ n)) (P? |> λ where
  (yes p) → map₂ inj₁ (iffM .from p)
  (no ¬p) → map₂ inj₂ (iffN .from ¬p))
... | n , inj₁ TMn = yes (iffM .to (n , TMn))
... | n , inj₂ TNn = no (iffN .to (n , TNn))

markov : SemiDec P → Stable P
markov sdp ¬¬p = reconstruct sdp (decidable-stable P? ¬¬p)
