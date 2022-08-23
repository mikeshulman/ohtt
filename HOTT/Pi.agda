{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Pi where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe
open import HOTT.Square

postulate
  kan-Π : (A : Type) (B : A → Type) →
    kan (Π A B) ≡ bury [≊] {Σ Type (λ X → X ⇒ Type)} (λ k → Π (fst k) (snd k ∙_)) (λ k₀ k₁ k₂ →
    ≊[ (λ f₀ f₁ → （ aₓ ⦂ （ a₀ ⦂ fst k₀ ）× （ a₁ ⦂ fst k₁ ）× (fst k₂ ↓ ／ a₀ ～ a₁) ）⇒
                    (snd k₂ ∙ (₁st aₓ , ₂nd aₓ , ₃rd' aₓ) ↓ ／ f₀ ∙ ₁st aₓ ～ f₁ ∙ ₂nd aₓ )) ,
       (ƛ f₀ ⇒ (ƛ a₁ ⇒ coe⇒ (snd k₂ ∙ (coe⇐ (fst k₂ ↓) ∙ a₁ , a₁ , push⇐ (fst k₂ ↓) ∙ a₁) ↓) ∙ (f₀ ∙ (coe⇐ (fst k₂ ↓) ∙ a₁)))) ,
       (ƛ f₁ ⇒ (ƛ a₀ ⇒ coe⇐ (snd k₂ ∙ (a₀ , coe⇒ (fst k₂ ↓) ∙ a₀ , push⇒ (fst k₂ ↓) ∙ a₀) ↓) ∙ (f₁ ∙ (coe⇒ (fst k₂ ↓) ∙ a₀)))) ,
       -- TODO: I think we need squares, and maybe symmetry, in arbitrary squares in the universe for this.
       (ƛ f₀ ⇒ ƛ aₓ ⇒ {!comp⇐ {coe⇐ (fst k₂ ↓) ∙ ₂nd aₓ} {₂nd aₓ} (push⇐ (fst k₂ ↓) ∙ ₂nd aₓ) {₁st aₓ} {₂nd aₓ} (₃rd' aₓ) (refl (₂nd aₓ))!}) ,
       (ƛ f₁ ⇒ {!!}) ]
    ) (A , 𝛌 B)
--{-# REWRITE kan-Π #-}
