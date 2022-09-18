module HOTT.Unit where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe.Parametric

postulate
  corr-refl-⊤ : corr ((★ , ★ , ★ , ⊤ , ⊤) , refl ⊤) ≡ (★ , (ƛ _ ⇒ ƛ _ ⇒ ⊤))
{-# REWRITE corr-refl-⊤ #-}

{-
postulate
  kan-⊤ : kan ⊤ ≡ bury [≊] {⊤} (λ _ → ⊤) (λ _ _ _ →
    ≊[ (λ _ _ → ⊤) , (ƛ x ⇒ x) , (ƛ x ⇒ x) , (ƛ _ ⇒ ★) , (ƛ _ ⇒ ★) ]
    ) ★
{-# REWRITE kan-⊤ #-}

-- We don't need to assert this; it holds by the η-law for ⊤.
sym-⊤ : {u₀₀ u₀₁ u₁₀ u₁₁ : ⊤} (u : ∂ ⊤ u₀₀ u₀₁ u₁₀ u₁₁) (u₂₂ : Sq ⊤ u) →
  sym ⊤ u u₂₂ ≡ ★
sym-⊤ u u₂₂ = reflᵉ
-}
