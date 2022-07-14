{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe.TopCompose where

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

-- This is a copy of HOTT.Universe.Top, but with an extra compostiion
-- ⊚ on the constant type family, since those families don't reduce
-- and hence can't be matched against an actual constant type family
-- like we have in Universe.Top.

postulate
  top-pop-pop-AP-const-U-⊚ : {Γ Δ Θ : Tel} (h : Δ ⇨ᵉ el Θ) (f : Γ ⇨ᵉ el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h))) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ top (f ⊘ᵉ (γ ₀))
  top-pop-AP-const-U-⊚ : {Γ Δ Θ : Tel} (h : Δ ⇨ᵉ el Θ) (f : Γ ⇨ᵉ el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h))) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ top (f ⊘ᵉ (γ ₁))

{-# REWRITE top-pop-pop-AP-const-U-⊚ top-pop-AP-const-U-⊚ #-}

postulate
  Id-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₀ : top (f (γ ₀))) (x₁ : top (f (γ ₁))) →
    Id (Λ x ⇨ top (f x)) γ x₀ x₁ ≡ (x₀ ~[ top (AP (Λ⇨ᵉ f) γ) ] x₁)

{-# REWRITE Id-top-⊚ #-}

postulate
  tr→-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₀ : top (f (γ ₀))) →
    tr→ (Λ x ⇨ top (f x)) γ x₀ ≡ coe⇒ (top (AP (Λ⇨ᵉ f) γ)) ∙ x₀
  tr←-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₁ : top (f (γ ₁))) →
    tr← (Λ x ⇨ top (f x)) γ x₁ ≡ coe⇐ (top (AP (Λ⇨ᵉ f) γ)) ∙ x₁

{-# REWRITE tr→-top-⊚ tr←-top-⊚ #-}

postulate
  lift→-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₀ : top (f (γ ₀))) →
    lift→ (Λ x ⇨ top (f x)) γ x₀ ≡ ~coe⇒ (top (AP (Λ⇨ᵉ f) γ)) x₀
  lift←-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₁ : top (f (γ ₁))) →
    lift← (Λ x ⇨ top (f x)) γ x₁ ≡ ~coe⇐ (top (AP (Λ⇨ᵉ f) γ)) x₁

{-# REWRITE lift→-top-⊚ lift←-top-⊚ #-}

postulate
  utr→-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₀ : top (f (γ ₀))) (x₁ x₁' : top (f (γ ₁)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀ x₁') →
    utr→ (Λ x ⇨ top (f x)) γ x₀ x₁ x₁' x₂ x₂' ≡ ucoe⇒ (top (AP (Λ⇨ᵉ f) γ)) x₀ x₁ x₁' x₂ x₂'
  utr←-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₁ : top (f (γ ₁))) (x₀ x₀' : top (f (γ ₀)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀' x₁) →
    utr← (Λ x ⇨ top (f x)) γ x₁ x₀ x₀' x₂ x₂' ≡ ucoe⇐ (top (AP (Λ⇨ᵉ f) γ)) x₁ x₀ x₀' x₂ x₂'

{-# REWRITE utr→-top-⊚ utr←-top-⊚ #-}

postulate
  ulift→-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₀ : top (f (γ ₀))) (x₁ x₁' : top (f (γ ₁)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀ x₁') →
    ulift→ (Λ x ⇨ top (f x)) γ x₀ x₁ x₁' x₂ x₂' ≡ u~coe⇒ (top (AP (Λ⇨ᵉ f) γ)) x₀ x₁ x₁' x₂ x₂'
  ulift←-top-⊚ : {Γ Δ Θ : Tel} (γ : el (ID Γ)) (h : Δ ⇨ᵉ el Θ) (f : el Γ → el (Δ ▸ ((Λ _ ⇨ Type) ⊚ h)))
    (x₁ : top (f (γ ₁))) (x₀ x₀' : top (f (γ ₀)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀' x₁) →
    ulift← (Λ x ⇨ top (f x)) γ x₁ x₀ x₀' x₂ x₂' ≡ u~coe⇐ (top (AP (Λ⇨ᵉ f) γ)) x₁ x₀ x₀' x₂ x₂'

{-# REWRITE ulift→-top-⊚ ulift←-top-⊚ #-}
