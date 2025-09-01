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
open import Data.Bool.Base hiding (_≤_; _<_)
open import Data.Bool.Properties hiding (≤-refl; <-wellFounded)

≢0⇒suc : ∀ {n} → n ≢ 0 → suc (pred n) ≡ n
≢0⇒suc {0} 0≢0 = ⊥-elim (0≢0 refl)
≢0⇒suc {suc _} _ = refl

μ′ : ∀ {ℓ} {P : ℕ → Set ℓ} → Decidable P → ∀ (@0 n) → @0 P n → @0 Acc _<_ n → ∃[ n ] P n
μ′ {_} {P} P? n Pn (acc rs) with P? 0
... | yes P0 = 0 , P0
... | no ¬P0 =
  let m , Psm = μ′ (P? ∘ suc) (pred n) Pspn (rs pn<n)
  in suc m , Psm
  where
    @0 n≢0 : n ≢ 0
    n≢0 refl = ¬P0 Pn

    @0 spn : suc (pred n) ≡ n
    spn = ≢0⇒suc n≢0

    @0 Pspn : P (suc (pred n))
    Pspn rewrite spn = Pn

    @0 pn<n : pred n < n
    pn<n rewrite spn = ≤-refl

μ : ∀ {ℓ} {P : ℕ → Set ℓ} → Decidable P → @0 ∃[ n ] P n → ∃[ n ] P n
μ P? (n , Pn) = μ′ P? n Pn (<-wellFounded n)

