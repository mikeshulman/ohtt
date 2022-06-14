{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sigma.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
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

{-
postulate
  utr→Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₀ : Σ (A (δ ₀)) (B (δ ₀))) (u₁ u₁' : Σ (A (δ ₁)) (B (δ ₁)))
    (u₂ : Id′ (λ w → Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → Σ (A w) (B w)) δ u₀ u₁') →
    utr→ (λ w → Σ (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    (utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂') ﹐
     coe← (Id′-AP {ε ▸ λ _ → A (δ ₁)} (λ x → (δ ₁) ∷ top x)
                    {[] ∷ π₁ u₁} {[] ∷ π₁ u₁'} ([] ∷ utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂'))
                    (uncurry B) (π₂ u₁) (π₂ u₁'))
        (comp→ {Δ ▸ A} (uncurry B) {(δ ₀) ∷ π₁ u₀} {(δ ₁) ∷ π₁ u₁} (δ ∷ π₁ u₂) {(δ ₀) ∷ π₁ u₀} {(δ ₁) ∷ π₁ u₁'} (δ ∷ π₁ u₂')
            (REFL (_∷_ {B = A} (δ ₀) (π₁ u₀))) (REFL (δ ₁) ∷ utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂'))
            (sq▸ A δ δ (REFL (δ ₀)) (REFL (δ ₁)) (DEGSQ-TB Δ δ)
                 (π₁ u₂) (π₁ u₂') (refl (π₁ u₀)) (utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂'))
                 (sym A (REFL (δ ₀)) (REFL (δ ₁)) δ δ (DEGSQ-LR Δ δ) (π₁ (refl u₀))
                        (utr→ A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂')) (π₁ u₂) (π₁ u₂')
                        (ulift→Sq A δ (π₁ u₀) (π₁ u₁) (π₁ u₁') (π₁ u₂) (π₁ u₂'))))
            {π₂ u₀} {π₂ u₁} (π₂ u₂) {π₂ u₀} {π₂ u₁'} (π₂ u₂')
            (coe→ (Id′-AP {ε} {Δ ▸ A} (λ _ → (δ ₀) ∷ π₁ u₀) {[]} {[]} [] (uncurry B) (π₂ u₀) (π₂ u₀)) (refl (π₂ u₀)))))
  utr←Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₁ : Σ (A (δ ₁)) (B (δ ₁))) (u₀ u₀' : Σ (A (δ ₀)) (B (δ ₀)))
    (u₂ : Id′ (λ w → Σ (A w) (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → Σ (A w) (B w)) δ u₀' u₁) →
    utr← (λ w → Σ (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    (utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂') ﹐
     coe← (Id′-AP {ε ▸ λ _ → A (δ ₀)} (λ x → (δ ₀) ∷ top x)
                    {[] ∷ π₁ u₀} {[] ∷ π₁ u₀'} ([] ∷ utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂'))
                    (uncurry B) (π₂ u₀) (π₂ u₀'))
        (comp← {Δ ▸ A} (uncurry B) {(δ ₀) ∷ π₁ u₀} {(δ ₁) ∷ π₁ u₁} (δ ∷ π₁ u₂) {(δ ₀) ∷ π₁ u₀'} {(δ ₁) ∷ π₁ u₁} (δ ∷ π₁ u₂')
            (REFL (δ ₀) ∷ utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂')) (REFL (_∷_ {B = A} (δ ₁) (π₁ u₁)))
            (sq▸ A δ δ (REFL (δ ₀)) (REFL (δ ₁)) (DEGSQ-TB Δ δ)
                 (π₁ u₂) (π₁ u₂') (utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂')) (refl (π₁ u₁))
                 (sym A (REFL (δ ₀)) (REFL (δ ₁)) δ δ (DEGSQ-LR Δ δ)
                        (utr← A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂'))
                        (π₁ (refl u₁)) (π₁ u₂) (π₁ u₂')
                        (ulift←Sq A δ (π₁ u₁) (π₁ u₀) (π₁ u₀') (π₁ u₂) (π₁ u₂'))))
            {π₂ u₀} {π₂ u₁} (π₂ u₂) {π₂ u₀'} {π₂ u₁} (π₂ u₂')
            (coe→ (Id′-AP {ε} {Δ ▸ A} (λ _ → (δ ₁) ∷ π₁ u₁) {[]} {[]} [] (uncurry B) (π₂ u₁) (π₂ u₁)) (refl (π₂ u₁)))))

{-# REWRITE utr→Σ utr←Σ #-}
-}
