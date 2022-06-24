{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Copy.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Copy.Base

------------------------------
-- Transport in copy-types
------------------------------

-- Transport in copy-types only computes after ↓ has been applied.

postulate
  tr→Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : Copy (A (δ ₀))) →
    tr→ (λ x → Copy (A x)) δ a₀ ↓ ≡ tr→ A δ (a₀ ↓)
  tr←Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : Copy (A (δ ₁))) →
    tr← (λ x → Copy (A x)) δ a₁ ↓ ≡ tr← A δ (a₁ ↓)

{-# REWRITE tr→Copy tr←Copy #-}

postulate
  lift→Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : Copy (A (δ ₀))) →
    lift→ (λ x → Copy (A x)) δ a₀ ↓ ≡ lift→ A δ (a₀ ↓)
  lift←Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : Copy (A (δ ₁))) →
    lift← (λ x → Copy (A x)) δ a₁ ↓ ≡ lift← A δ (a₁ ↓)

{-# REWRITE lift→Copy lift←Copy #-}

-- Copy-types are also simple enough that we can actually compute utr
-- and ulift directly.

postulate
  utr→Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : Copy (A (δ ₀))) →
    (a₁ a₁' : Copy (A (δ ₁))) (a₂ : Id′ (λ x → Copy (A x)) δ a₀ a₁) (a₂' : Id′ (λ x → Copy (A x)) δ a₀ a₁') →
    utr→ (λ x → Copy (A x)) δ a₀ a₁ a₁' a₂ a₂' ↓ ≡ utr→ A δ (a₀ ↓) (a₁ ↓) (a₁' ↓) (a₂ ↓) (a₂' ↓)
  utr←Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : Copy (A (δ ₁))) →
    (a₀ a₀' : Copy (A (δ ₀))) (a₂ : Id′ (λ x → Copy (A x)) δ a₀ a₁) (a₂' : Id′ (λ x → Copy (A x)) δ a₀' a₁) →
    utr← (λ x → Copy (A x)) δ a₁ a₀ a₀' a₂ a₂' ↓ ≡ utr← A δ (a₁ ↓) (a₀ ↓) (a₀' ↓) (a₂ ↓) (a₂' ↓)

{-# REWRITE utr→Copy utr←Copy #-}

postulate
  ulift→Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : Copy (A (δ ₀))) →
    (a₁ a₁' : Copy (A (δ ₁))) (a₂ : Id′ (λ x → Copy (A x)) δ a₀ a₁) (a₂' : Id′ (λ x → Copy (A x)) δ a₀ a₁') →
    ulift→ (λ x → Copy (A x)) δ a₀ a₁ a₁' a₂ a₂' ↓ ≡
      coe→ (Id′-AP (λ x → pop x ∷ (top x ↓)) ([] ∷ a₁ ∷ a₁' ∷ utr→ (λ x → Copy (A x)) δ a₀ a₁ a₁' a₂ a₂')
                    (λ x → Id′ A δ (a₀ ↓) (top x)) (a₂ ↓) (a₂' ↓))
            (ulift→ A δ (a₀ ↓) (a₁ ↓) (a₁' ↓) (a₂ ↓) (a₂' ↓))
  ulift←Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₁ : Copy (A (δ ₁))) →
    (a₀ a₀' : Copy (A (δ ₀))) (a₂ : Id′ (λ x → Copy (A x)) δ a₀ a₁) (a₂' : Id′ (λ x → Copy (A x)) δ a₀' a₁) →
    ulift← (λ x → Copy (A x)) δ a₁ a₀ a₀' a₂ a₂' ↓ ≡
      coe→ (Id′-AP (λ x → pop x ∷ (top x ↓)) ([] ∷ a₀ ∷ a₀' ∷ utr← (λ x → Copy (A x)) δ a₁ a₀ a₀' a₂ a₂')
                    (λ x → Id′ A δ (top x) (a₁ ↓)) (a₂ ↓) (a₂' ↓))
            (ulift← A δ (a₁ ↓) (a₀ ↓) (a₀' ↓) (a₂ ↓) (a₂' ↓))

{-# REWRITE ulift→Copy ulift←Copy #-}
