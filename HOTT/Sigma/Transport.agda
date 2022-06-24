{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Sigma.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Transport
open import HOTT.Fill
open import HOTT.Sigma.Base

----------------------------------------
-- Transport in Σ-types
----------------------------------------

postulate
  tr→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (B (δ ₀))) →
    tr→ (λ w → Σ (A w) (B w)) δ u₀ ≡
    (tr→ A δ (π₁ u₀) ﹐  tr→ {Δ ▸ A} (uncurry B) (δ ∷ π₁ u₀ ∷ tr→ A δ (π₁ u₀) ∷ lift→ A δ (π₁ u₀)) (π₂ u₀))
  tr←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₁ : Σ (A (δ ₁)) (B (δ ₁))) →
    tr← (λ w → Σ (A w) (B w)) δ u₁ ≡
    (tr← A δ (π₁ u₁) ﹐ tr← {Δ ▸ A} (uncurry B) (δ ∷ tr← A δ (π₁ u₁) ∷ π₁ u₁ ∷ lift← A δ (π₁ u₁)) (π₂ u₁))

{-# REWRITE tr→Σ tr←Σ #-}

postulate
  lift→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (B (δ ₀))) →
    lift→ (λ w → Σ (A w) (B w)) δ u₀ ≡
    (lift→ A δ (π₁ u₀) ﹐  lift→ {Δ ▸ A} (uncurry B) (δ ∷ π₁ u₀ ∷ tr→ A δ (π₁ u₀) ∷ lift→ A δ (π₁ u₀)) (π₂ u₀))
  lift←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₁ : Σ (A (δ ₁)) (B (δ ₁))) →
    lift← (λ w → Σ (A w) (B w)) δ u₁ ≡
    (lift← A δ (π₁ u₁) ﹐  lift← {Δ ▸ A} (uncurry B) (δ ∷ tr← A δ (π₁ u₁) ∷ π₁ u₁ ∷ lift← A δ (π₁ u₁)) (π₂ u₁))

{-# REWRITE lift→Σ lift←Σ #-}

-- Once we've defined tr and lift for Σ-types, we can deduce utr and
-- ulift from square-filling.  Since that involves transport in an
-- identity type of a Σ-type, which is again a Σ-type, the above
-- definitions should suffice to compute it.

postulate
  utr→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₀ : Σ (A (δ ₀)) (B (δ ₀))) (u₁ u₁' : Σ (A (δ ₁)) (B (δ ₁)))
    (u₂ : Id (λ w → Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id (λ w → Σ (A w) (B w)) δ u₀ u₁') →
    utr→      (λ w → Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-utr→ (λ w → Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂'
  utr←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₁ : Σ (A (δ ₁)) (B (δ ₁))) (u₀ u₀' : Σ (A (δ ₀)) (B (δ ₀)))
    (u₂ : Id (λ w → Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id (λ w → Σ (A w) (B w)) δ u₀' u₁) →
    utr←      (λ w → Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-utr← (λ w → Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE utr→Σ utr←Σ #-}

postulate
  ulift→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₀ : Σ (A (δ ₀)) (B (δ ₀))) (u₁ u₁' : Σ (A (δ ₁)) (B (δ ₁)))
    (u₂ : Id (λ w → Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id (λ w → Σ (A w) (B w)) δ u₀ u₁') →
    ulift→      (λ w → Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-ulift→ (λ w → Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂'
  ulift←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₁ : Σ (A (δ ₁)) (B (δ ₁))) (u₀ u₀' : Σ (A (δ ₀)) (B (δ ₀)))
    (u₂ : Id (λ w → Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id (λ w → Σ (A w) (B w)) δ u₀' u₁) →
    ulift←      (λ w → Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-ulift← (λ w → Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE ulift→Σ ulift←Σ #-}
