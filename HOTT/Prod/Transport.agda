{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Prod.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Prod.Base

----------------------------------------
-- Transport in product types
----------------------------------------

postulate
  tr→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₀ : A (δ ₀) × B (δ ₀)) →
    tr→ (λ w → A w × B w) δ u₀ ≡ (tr→ A δ (fst u₀) , tr→ B δ (snd u₀))
  tr←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₁ : A (δ ₁) × B (δ ₁)) →
    tr← (λ w → A w × B w) δ u₁ ≡ (tr← A δ (fst u₁) , tr← B δ (snd u₁))

{-# REWRITE tr→× tr←× #-}

postulate
  lift→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₀ : A (δ ₀) × B (δ ₀)) →
    lift→ (λ w → A w × B w) δ u₀ ≡ (lift→ A δ (fst u₀) , lift→ B δ (snd u₀))
  lift←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (u₁ : A (δ ₁) × B (δ ₁)) →
    lift← (λ w → A w × B w) δ u₁ ≡ (lift← A δ (fst u₁) , lift← B δ (snd u₁))

{-# REWRITE lift→× lift←× #-}

-- Product types are still simple enough that it's feasible to define
-- utr and ulift explicitly rather than by way of square composites
-- and filling.  We do this to make the point.

postulate
  utr→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : A (δ ₀) × B (δ ₀)) (u₁ u₁' : A (δ ₁) × B (δ ₁))
    (u₂ : Id′ (λ w → A w × B w) δ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ u₀ u₁') →
    utr→ (λ w → A w × B w) δ u₀ u₁ u₁' u₂ u₂' ≡
    (utr→ A δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') , utr→ B δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂'))
  utr←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : A (δ ₁) × B (δ ₁)) (u₀ u₀' : A (δ ₀) × B (δ ₀))
    (u₂ : Id′ (λ w → A w × B w) δ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ u₀' u₁) →
    utr← (λ w → A w × B w) δ u₁ u₀ u₀' u₂ u₂' ≡
    (utr← A δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') , utr← B δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂'))

{-# REWRITE utr→× utr←× #-}

postulate
  ulift→× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : A (δ ₀) × B (δ ₀)) (u₁ u₁' : A (δ ₁) × B (δ ₁))
    (u₂ : Id′ (λ w → A w × B w) δ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ u₀ u₁') →
    ulift→ (λ w → A w × B w) δ u₀ u₁ u₁' u₂ u₂' ≡
    (coe→ (Id′-AP▸ {ε ▸ (λ _ → A (δ ₁) × B (δ ₁))} {ε} (λ _ → A (δ ₁))
              (λ _ → []) (λ x → fst (top x))
              ([] ∷ u₁ ∷ u₁' ∷
               (utr→ (λ z → A z) δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') ,
                utr→ (λ z → B z) δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
              (λ w → Id′ A δ (fst u₀) (top w))
              (fst u₂) (fst u₂'))
           (ulift→ A δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂')),
     coe→ (Id′-AP▸ {ε ▸ (λ _ → A (δ ₁) × B (δ ₁))} {ε} (λ _ → B (δ ₁))
              (λ _ → []) (λ x → snd (top x))
              ([] ∷ u₁ ∷ u₁' ∷
               (utr→ (λ z → A z) δ (fst u₀) (fst u₁) (fst u₁') (fst u₂) (fst u₂') ,
                utr→ (λ z → B z) δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
              (λ w → Id′ B δ (snd u₀) (top w))
              (snd u₂) (snd u₂'))
           (ulift→ B δ (snd u₀) (snd u₁) (snd u₁') (snd u₂) (snd u₂')))
  ulift←× : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : A (δ ₁) × B (δ ₁)) (u₀ u₀' : A (δ ₀) × B (δ ₀))
    (u₂ : Id′ (λ w → A w × B w) δ u₀ u₁) (u₂' : Id′ (λ w → A w × B w) δ u₀' u₁) →
    ulift← (λ w → A w × B w) δ u₁ u₀ u₀' u₂ u₂' ≡
    (coe→ (Id′-AP▸ {ε ▸ (λ _ → A (δ ₀) × B (δ ₀))} {ε} (λ _ → A (δ ₀))
              (λ _ → []) (λ x → fst (top x))
              ([] ∷ u₀ ∷ u₀' ∷
               (utr← (λ z → A z) δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') ,
                utr← (λ z → B z) δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂')))
              (λ w → Id′ A δ (top w) (fst u₁))
              (fst u₂) (fst u₂'))
           (ulift← A δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂')),
     coe→ (Id′-AP▸ {ε ▸ (λ _ → A (δ ₀) × B (δ ₀))} {ε} (λ _ → B (δ ₀))
              (λ _ → []) (λ x → snd (top x))
              ([] ∷ u₀ ∷ u₀' ∷
               (utr← (λ z → A z) δ (fst u₁) (fst u₀) (fst u₀') (fst u₂) (fst u₂') ,
                utr← (λ z → B z) δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂')))
              (λ w → Id′ B δ (top w) (snd u₁))
              (snd u₂) (snd u₂'))
           (ulift← B δ (snd u₁) (snd u₀) (snd u₀') (snd u₂) (snd u₂')))

{-# REWRITE ulift→× ulift←× #-}
