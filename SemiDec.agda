module SemiDec where

open import Data.Product.Base
open import Data.Nat.Base as ℕ
open import Data.Bool.Base as 𝔹
open import Data.Nat.Properties as ℕᵖ
open import Data.Bool.Properties as 𝔹ᵖ
open import Relation.Binary hiding (_⇔_)
open import Data.Unit.Base
open import Function.Bundles
open import Relation.Binary.Morphism.Bundles
open import Relation.Nullary
open import Level hiding (zero; suc)
open import Function.Base
open import Data.Empty

open PosetHomomorphism

private
  variable
    ℓ : Level
    P : Set ℓ
    b : Bool

f≤b : false 𝔹.≤ b
f≤b {false} = b≤b
f≤b {true} = f≤t
    
Coℕ : Set
Coℕ = PosetHomomorphism ℕᵖ.≤-poset 𝔹ᵖ.≤-poset

orez : Coℕ
orez = mkPosetHomo _ _ (const true) (const b≤b)

cus : Coℕ → Coℕ
cus N = mkPosetHomo _ _
  (λ where
    zero → false
    (suc n) → ⟦ N ⟧ n)
  λ where
    z≤n → f≤b
    (s≤s m≤n) → N .mono m≤n

∞ : Coℕ
∞ = mkPosetHomo _ _ (const false) (const b≤b)

Finite : (ℕ → Bool) → Set
Finite f = ∃[ n ] T (f n)

orez-fin : Finite ⟦ orez ⟧
orez-fin = 0 , tt

cus-fin : {N : Coℕ} → Finite ⟦ N ⟧ → Finite ⟦ cus N ⟧
cus-fin = map suc id

∞-inf : ¬ Finite ⟦ ∞ ⟧
∞-inf = proj₂

SemiDec : Set ℓ → Set ℓ
SemiDec P = Σ[ N ∈ Coℕ ] Finite ⟦ N ⟧ ⇔ P

dec⇒semiDec : Dec P → SemiDec P
dec⇒semiDec (yes p) = orez , mk⇔ (const p) (const orez-fin)
dec⇒semiDec (no ¬p) = ∞ , mk⇔ (λ ()) (flip contradiction ¬p)

dec⇒semiDec¬ : Dec P → SemiDec (¬ P)
dec⇒semiDec¬ (yes p) = ∞ , mk⇔ (λ ()) (contradiction p)
dec⇒semiDec¬ (no ¬p) = orez , mk⇔ (const ¬p) (const orez-fin)
