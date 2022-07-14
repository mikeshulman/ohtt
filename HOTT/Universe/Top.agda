{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Sigma
open import HOTT.Pi
open import HOTT.Copy
open import HOTT.Groupoids
open import HOTT.Universe.Base

postulate
  tr→-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) →
    tr→ (Λ x ⇨ top (f x)) γ x₀ ≡ fst (fst (fst (snd (top (AP (Λ⇨ᵉ f) γ) ↓)) ∙ x₀))
  tr←-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₁ : top (f (γ ₁))) →
    tr← (Λ x ⇨ top (f x)) γ x₁ ≡ fst (fst (snd (snd (top (AP (Λ⇨ᵉ f) γ) ↓)) ∙ x₁))

{-# REWRITE tr→-top tr←-top #-}

postulate
  lift→-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) →
    lift→ (Λ x ⇨ top (f x)) γ x₀ ≡ snd (fst (fst (snd (top (AP (Λ⇨ᵉ f) γ) ↓)) ∙ x₀))
  lift←-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₁ : top (f (γ ₁))) →
    lift← (Λ x ⇨ top (f x)) γ x₁ ≡ snd (fst (snd (snd (top (AP (Λ⇨ᵉ f) γ) ↓)) ∙ x₁))

{-# REWRITE lift→-top lift←-top #-}

postulate
  utr→-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) (x₁ x₁' : top (f (γ ₁)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀ x₁') →
    utr→ (Λ x ⇨ top (f x)) γ x₀ x₁ x₁' x₂ x₂' ≡ fst (snd (fst (snd (top (AP (Λ⇨ᵉ f) γ) ↓)) ∙ x₀) ∙ (x₁ , x₂) ∙ (x₁' , x₂'))
  utr←-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₁ : top (f (γ ₁))) (x₀ x₀' : top (f (γ ₀)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀' x₁) →
    utr← (Λ x ⇨ top (f x)) γ x₁ x₀ x₀' x₂ x₂' ≡ fst (snd (snd (snd (top (AP (Λ⇨ᵉ f) γ) ↓)) ∙ x₁) ∙ (x₀ , x₂) ∙ (x₀' , x₂'))

{-# REWRITE utr→-top utr←-top #-}

postulate
  ulift→-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) (x₁ x₁' : top (f (γ ₁)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀ x₁') →
    ulift→ (Λ x ⇨ top (f x)) γ x₀ x₁ x₁' x₂ x₂' ≡ snd (snd (fst (snd (top (AP (Λ⇨ᵉ f) γ) ↓)) ∙ x₀) ∙ (x₁ , x₂) ∙ (x₁' , x₂'))
  ulift←-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₁ : top (f (γ ₁))) (x₀ x₀' : top (f (γ ₀)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀' x₁) →
    ulift← (Λ x ⇨ top (f x)) γ x₁ x₀ x₀' x₂ x₂' ≡ snd (snd (snd (snd (top (AP (Λ⇨ᵉ f) γ) ↓)) ∙ x₁) ∙ (x₀ , x₂) ∙ (x₀' , x₂'))

{-# REWRITE ulift→-top ulift←-top #-}
