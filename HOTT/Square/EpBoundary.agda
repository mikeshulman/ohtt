{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Square.EpBoundary where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Square.Base

-- We do seem to need special versions of sq∷₀₂ and sq∷₁₂ in the case when Δ is ε.

postulate
  sq[]∷₀₂ : (A : Type)
    {a₀₀ : A} {a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁)
    {a₁₀ : A} {a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
    (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁)
    (a₂₂ : Sq (Λ _ ⇨ A) [] a₀₂ a₁₂ a₂₀ a₂₁) →
    AP (Λ₀ {ε▸ A}) ([] ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) ≡ᵉ [] ∷ a₀₀ ∷ a₀₁ ∷ a₀₂
  sq[]∷₁₂ : (A : Type)
    {a₀₀ : A} {a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁)
    {a₁₀ : A} {a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
    (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁)
    (a₂₂ : Sq (Λ _ ⇨ A) [] a₀₂ a₁₂ a₂₀ a₂₁) →
    AP (Λ₁ {ε▸ A}) ([] ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂ ∷ a₂₀ ∷ a₂₁ ∷ a₂₂) ≡ᵉ [] ∷ a₁₀ ∷ a₁₁ ∷ a₁₂

{-# REWRITE sq[]∷₀₂ sq[]∷₁₂ #-}

