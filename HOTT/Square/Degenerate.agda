{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Square.Degenerate where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Transport
open import HOTT.Square

----------------------------------------
-- Degenerate squares
----------------------------------------

-- Top-bottom degenerate squares in a context
DEGSQ-TB : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → el (SQ Δ δ₂ δ₂ (REFL δ₀) (REFL δ₁))
DEGSQ-TB Δ {δ₀} {δ₁} δ₂ =
  COE← (ID′-AP {Δ} {PROD Δ Δ} (λ w → PR Δ Δ w w) δ₂ (UID Δ) (REFL δ₀) (REFL δ₁))
       (AP′ {Δ} (λ w → ID Δ w w) REFL δ₂)

-- Left-right degenerate squares in a context
DEGSQ-LR : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → el (SQ Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂)
DEGSQ-LR Δ {δ₀} {δ₁} δ₂ = COE← (ID′-AP {ε} (λ _ → PR Δ Δ δ₀ δ₁) [] (UID Δ) δ₂ δ₂) (REFL δ₂)

{-
ulift→Sq : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀)
  (a₁ a₁' : A δ₁) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') →
  Sq A (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂) (refl a₀) (utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
ulift→Sq {Δ} A {δ₀} {δ₁} δ₂ a₀ a₁ a₁' a₂ a₂' =
  {! coe← (Id′-AP {ε ▸ λ _ → A δ₁}
               {PROD Δ Δ ► UID Δ ▸ (λ w → A (FST Δ Δ (POP (UID Δ) w))) ▸ (λ w → A (SND Δ Δ (POP (UID Δ) (pop w))))}
               (λ w → PAIR (UID Δ) (PR Δ Δ δ₀ δ₁) δ₂ ∷ a₀ ∷ top w)
               {[] ∷ a₁} {[] ∷ a₁'}
               ([] ∷ utr→ A δ₂ a₀ a₁ a₁' a₂ a₂')
            (λ z → Id′ A (TOP (UID Δ) (pop (pop z))) (top (pop z)) (top z)) a₂ a₂')
        (ulift→ A δ₂ a₀ a₁ a₁' a₂ a₂')!}
-}
