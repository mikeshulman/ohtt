module HOTT.Sigma where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe

postulate
  kan-Σ : (A : Type) (B : A → Type) →
    kan (Σ A B) ≡ bury [≊] {Σ Type (λ X → X ⇒ Type)} (λ k → Σ (fst k) (snd k ∙_)) (λ k₀ k₁ k₂ →
    ≊[ (λ u₀ u₁ → （ e₀ ⦂ fst k₂ ↓ ／ fst u₀ ～ fst u₁ ）× (snd k₂ ∙ (fst u₀ , fst u₁ , e₀) ↓ ／ snd u₀ ～ snd u₁) ) ,
       (ƛ u₀ ⇒ coe⇒ (fst k₂ ↓) ∙ fst u₀  , coe⇒ (snd k₂ ∙ (fst u₀ , coe⇒ (fst k₂ ↓) ∙ fst u₀ , push⇒ (fst k₂ ↓) ∙ fst u₀) ↓) ∙ snd u₀) ,
       (ƛ u₁ ⇒ coe⇐ (fst k₂ ↓) ∙ fst u₁  , coe⇐ (snd k₂ ∙ (coe⇐ (fst k₂ ↓) ∙ fst u₁ , fst u₁ , push⇐ (fst k₂ ↓) ∙ fst u₁) ↓) ∙ snd u₁) ,
       (ƛ u₀ ⇒ push⇒ (fst k₂ ↓) ∙ fst u₀ , push⇒ (snd k₂ ∙ (fst u₀ , coe⇒ (fst k₂ ↓) ∙ fst u₀ , push⇒ (fst k₂ ↓) ∙ fst u₀) ↓) ∙ snd u₀) ,
       (ƛ u₁ ⇒ push⇐ (fst k₂ ↓) ∙ fst u₁ , push⇐ (snd k₂ ∙ (coe⇐ (fst k₂ ↓) ∙ fst u₁ , fst u₁ , push⇐ (fst k₂ ↓) ∙ fst u₁) ↓) ∙ snd u₁) ]
    ) (A , 𝛌 B)
{-# REWRITE kan-Σ #-}
