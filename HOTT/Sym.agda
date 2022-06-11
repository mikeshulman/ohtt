{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square

------------------------------
-- Symmetry
------------------------------

postulate
  SYM : (Δ : Tel) → el (SQ Δ) → el (SQ Δ)
  SYM₀₂ : (Δ : Tel) (δ : el (SQ Δ)) → AP _₀ (SYM Δ δ) ≡ δ ₂₀
  SYM₂₀ : (Δ : Tel) (δ : el (SQ Δ)) → (SYM Δ δ) ₀ ≡ δ ₀₂
  SYM₁₂ : (Δ : Tel) (δ : el (SQ Δ)) → AP _₁ (SYM Δ δ) ≡ δ ₂₁
  SYM₂₁ : (Δ : Tel) (δ : el (SQ Δ)) → (SYM Δ δ) ₁ ≡ δ ₁₂
  SYM-SYM : (Δ : Tel) (δ : el (SQ Δ)) → SYM Δ (SYM Δ δ) ≡ δ

{-# REWRITE SYM₀₂ SYM₂₀ SYM₁₂ SYM₂₁ SYM-SYM #-}

postulate
  AP-REFL≡SYM-REFL : (Γ Δ : Tel) (f : el Γ → el Δ) (γ : el (ID Γ)) →
    AP (λ x → REFL (f x)) γ ≡ SYM Δ (REFL (AP f γ))

{-# REWRITE AP-REFL≡SYM-REFL #-}

postulate
  sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
        {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
        {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
        (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
        Sq A δ a₀₂ a₁₂ a₂₀ a₂₁ → Sq A (SYM Δ δ) a₂₀ a₂₁ a₀₂ a₁₂
  sym-sym : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
        {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
        {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
        (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
        sym A (SYM Δ δ) a₂₀ a₂₁ a₀₂ a₁₂ (sym A δ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂) ≡ a₂₂

{-# REWRITE sym-sym #-}

{-
postulate
  -- This may seem the natural way to formulate the AP-REFL rule:
  AP-REFL-SYM : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    DEGSQ-TB Δ δ₂ ≡ SYM Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂)
-}
  -- However, since DEGSQ-TB involves a coercion, to make this rule
  -- computational it may be better to transfer that coercion to the RHS.
{-
  AP-REFL-SYM : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    AP′ {Δ} (λ w → ID Δ w w) REFL δ₂ ≡
      COE→ (ID′-AP {Δ} {PROD Δ Δ} (λ w → PR Δ Δ w w) δ₂ (UID Δ) (REFL δ₀) (REFL δ₁))
           (SYM Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂))
-}
{-
  -- On the other hand, so far it seems that these are more practical.
  SYM-DEGSQ-LR : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    SYM Δ (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂) ≡ DEGSQ-TB Δ δ₂
  SYM-DEGSQ-TB : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    SYM Δ δ₂ δ₂ (REFL δ₀) (REFL δ₁) (DEGSQ-TB Δ δ₂) ≡ DEGSQ-LR Δ δ₂

{-# REWRITE SYM-DEGSQ-LR SYM-DEGSQ-TB #-}
-}
{-
postulate
  ap-refl : {Δ : Tel} {A : el Δ → Type} (f : (x : el Δ) → A x)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ} (λ w → refl (f w)) {δ₀} {δ₁} δ₂ ≡
    {!sym A (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂) (refl (f δ₀)) (refl (f δ₁)) (ap f δ₂) (ap f δ₂)!}
-}
