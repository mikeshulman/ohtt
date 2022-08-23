{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Unit where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe
open import HOTT.Square

postulate
  kan-⊤ : kan ⊤ ≡ bury [≊] {⊤} (λ _ → ⊤) (λ _ _ _ →
    ≊[ (λ _ _ → ⊤) , (ƛ x ⇒ x) , (ƛ x ⇒ x) , (ƛ _ ⇒ ★) , (ƛ _ ⇒ ★) ]
    ) ★
{-# REWRITE kan-⊤ #-}

-- We don't need to assert this; it holds by the η-law for ⊤.
sym-⊤ : {u₀₀ u₀₁ u₁₀ u₁₁ : ⊤} (u : ∂ ⊤ u₀₀ u₀₁ u₁₀ u₁₁) (u₂₂ : Sq ⊤ u) →
  sym ⊤ u u₂₂ ≡ ★
sym-⊤ u u₂₂ = reflᵉ
