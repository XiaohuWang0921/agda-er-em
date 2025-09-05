module ConsAna where

open import Data.Nat.Base
open import Data.Bool.Base
open import Function.Base
open import Data.List.Base
open import Relation.Binary.PropositionalEquality
open import Data.List.Properties

-- pattern synonyms for better readability

pattern 0b = false
pattern 1b = true

-- Binary sequences

FBS = List Bool
IBS = ℕ → Bool

-- Restrictions

resFBS : FBS → ℕ → FBS
resFBS = flip take

resIBS : IBS → ℕ → FBS
resIBS _ 0 = []
resIBS α (suc n) = α 0 ∷ resIBS (α ∘ suc) n

-- Length

∣_∣ : FBS → ℕ
∣_∣ = length

-- Lengths of restrictions

∣resFBS∣ : ∀ u n → ∣ resFBS u n ∣ ≡ n ⊓ ∣ u ∣
∣resFBS∣ = flip length-take

∣resIBS∣ : ∀ α n → ∣ resIBS α n ∣ ≡ n
∣resIBS∣ α 0 = refl
∣resIBS∣ α (suc n) = cong suc (∣resIBS∣ (α ∘ suc) n)

-- Repeated restrictions

resFBS-idem : ∀ u m n → resFBS (resFBS u m) n ≡ resFBS u (n ⊓ m)
resFBS-idem = flip (flip ∘ flip take-take)

resIBS-idem : ∀ α m n → resFBS (resIBS α m) n ≡ resIBS α (n ⊓ m)
resIBS-idem α m 0 = refl
resIBS-idem α 0 (suc _) = refl
resIBS-idem α (suc m) (suc n) = cong (_ ∷_) (resIBS-idem (α ∘ suc) m n)
