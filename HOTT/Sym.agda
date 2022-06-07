{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Sym where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square
open import HOTT.Square.Degenerate

------------------------------
-- Symmetry
------------------------------

postulate
  SYM : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
    (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) →
    el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁) → el (SQ Δ δ₂₀ δ₂₁ δ₀₂ δ₁₂)
  SYM-SYM : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
    (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁)) →
    SYM Δ δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) ≡ δ₂₂

{-# REWRITE SYM-SYM #-}

postulate
  sym : {Δ : Tel} (A : el Δ → Type)
        {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
        (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
        {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
        (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
        Sq A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁ → Sq A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂ a₁₂
  sym-sym : {Δ : Tel} (A : el Δ → Type)
            {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
            (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
            {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
            (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) (a₂₂ : Sq A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁) →
            sym A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂ a₁₂ (sym A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂) ≡ a₂₂

{-# REWRITE sym-sym #-}

-- This may seem the natural way to formulate the AP-REFL rule:
{-
  AP-REFL-SYM : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    DEGSQ-TB Δ δ₂ ≡ SYM Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂)
-}
-- However, since DEGSQ-TB involves a coercion, to make this rule
-- computational it's better to transfer that coercion to the RHS.
postulate
  AP-REFL-SYM : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    AP′ {Δ} (λ w → ID Δ w w) REFL δ₂ ≡
      COE→ (ID′-AP {Δ} {PROD Δ Δ} (λ w → PR Δ Δ w w) δ₂ (UID Δ) (REFL δ₀) (REFL δ₁))
           (SYM Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂))

{-# REWRITE AP-REFL-SYM #-}

{-
postulate
  ap-refl : {Δ : Tel} {A : el Δ → Type} (f : (x : el Δ) → A x)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ} (λ w → refl (f w)) {δ₀} {δ₁} δ₂ ≡
    {!sym A (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂) (refl (f δ₀)) (refl (f δ₁)) (ap f δ₂) (ap f δ₂)!}
-}
