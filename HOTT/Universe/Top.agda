{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe.Top where

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

----------------------------------------
-- Identity types of type variables
----------------------------------------

-- Id-top, below, depends for its well-typedness on top-pop-pop-AP and
-- top-pop-AP applied at a constant family on the universe.  But even
-- top-pop-pop-AP-const doesn't help, because ＝U reduces even
-- further.  So we declare some additional special rewrites.  (This
-- same problem would happen with any other use of top-pop-pop-AP and
-- top-pop-AP at a particular type, but this is the only place so far
-- where we've needed such a thing.)
postulate
  top-pop-pop-AP-const-U : {Γ Δ : Tel} (f : Γ ⇨ᵉ el (Δ ▸ (Λ _ ⇨ Type))) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ top (f ⊘ᵉ (γ ₀))
  top-pop-AP-const-U : {Γ Δ : Tel} (f : Γ ⇨ᵉ el (Δ ▸ (Λ _ ⇨ Type))) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ top (f ⊘ᵉ (γ ₁))

{-# REWRITE top-pop-pop-AP-const-U top-pop-AP-const-U #-}

postulate
  Id-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) (x₁ : top (f (γ ₁))) →
    Id (Λ x ⇨ top (f x)) γ x₀ x₁ ≡ (x₀ ~[ top (AP (Λ⇨ᵉ f) γ) ] x₁)

{-# REWRITE Id-top #-}

postulate
  tr→-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) →
    tr→ (Λ x ⇨ top (f x)) γ x₀ ≡ coe⇒ (top (AP (Λ⇨ᵉ f) γ)) ∙ x₀
  tr←-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₁ : top (f (γ ₁))) →
    tr← (Λ x ⇨ top (f x)) γ x₁ ≡ coe⇐ (top (AP (Λ⇨ᵉ f) γ)) ∙ x₁

{-# REWRITE tr→-top tr←-top #-}

postulate
  lift→-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) →
    lift→ (Λ x ⇨ top (f x)) γ x₀ ≡ ~coe⇒ (top (AP (Λ⇨ᵉ f) γ)) x₀
  lift←-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₁ : top (f (γ ₁))) →
    lift← (Λ x ⇨ top (f x)) γ x₁ ≡ ~coe⇐ (top (AP (Λ⇨ᵉ f) γ)) x₁

{-# REWRITE lift→-top lift←-top #-}

postulate
  utr→-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) (x₁ x₁' : top (f (γ ₁)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀ x₁') →
    utr→ (Λ x ⇨ top (f x)) γ x₀ x₁ x₁' x₂ x₂' ≡ ucoe⇒ (top (AP (Λ⇨ᵉ f) γ)) x₀ x₁ x₁' x₂ x₂'
  utr←-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₁ : top (f (γ ₁))) (x₀ x₀' : top (f (γ ₀)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀' x₁) →
    utr← (Λ x ⇨ top (f x)) γ x₁ x₀ x₀' x₂ x₂' ≡ ucoe⇐ (top (AP (Λ⇨ᵉ f) γ)) x₁ x₀ x₀' x₂ x₂'

{-# REWRITE utr→-top utr←-top #-}

postulate
  ulift→-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) (x₁ x₁' : top (f (γ ₁)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀ x₁') →
    ulift→ (Λ x ⇨ top (f x)) γ x₀ x₁ x₁' x₂ x₂' ≡ u~coe⇒ (top (AP (Λ⇨ᵉ f) γ)) x₀ x₁ x₁' x₂ x₂'
  ulift←-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₁ : top (f (γ ₁))) (x₀ x₀' : top (f (γ ₀)))
    (x₂ : Id (Λ x ⇨ top (f x)) γ x₀ x₁) (x₂' : Id (Λ x ⇨ top (f x)) γ x₀' x₁) →
    ulift← (Λ x ⇨ top (f x)) γ x₁ x₀ x₀' x₂ x₂' ≡ u~coe⇐ (top (AP (Λ⇨ᵉ f) γ)) x₁ x₀ x₀' x₂ x₂'

{-# REWRITE ulift→-top ulift←-top #-}
