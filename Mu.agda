module Mu where

open import Data.Nat.Base
open import Data.Product
open import Relation.Unary
open import Relation.Nullary
open import Data.Empty
open import Function.Base
open import Induction.WellFounded
open import Data.Nat.Induction
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Data.Bool.Base hiding (_<_)
open import Data.Bool.Properties hiding (<-wellFounded)

≢0⇒suc : ∀ {n} → n ≢ 0 → n ≡ suc (pred n)
≢0⇒suc {0} 0≢0 = ⊥-elim (0≢0 refl)
≢0⇒suc {suc _} _ = refl

μ′ : ∀ {ℓ} {P : ℕ → Set ℓ} → Decidable P → (@0 (n , Pn) : ∃[ n ] P n) → @0 Acc _<_ n → ∃[ n ] P n
μ′ {_} {P} P? (n , Pn) (acc rs) with P? 0
... | yes P0 = 0 , P0
... | no ¬P0 =
  let m , Psuc-m = ∃-P-suc
  in suc m , Psuc-m
  where
    @0 n≢0 : n ≢ 0
    n≢0 refl = ¬P0 Pn

    @0 n-suc : n ≡ suc (pred n)
    n-suc = ≢0⇒suc n≢0

    ∃-P-suc : ∃[ m ] P (suc m)
    ∃-P-suc = μ′ (P? ∘ suc) (pred n , subst P n-suc Pn) (rs (subst (pred n <_) (sym n-suc) (n<1+n _)))

μ : ∀ {ℓ} {P : ℕ → Set ℓ} → Decidable P → @0 ∃[ n ] P n → ∃[ n ] P n
μ P? ∃P = μ′ P? ∃P (<-wellFounded (∃P .proj₁))

