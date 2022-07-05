{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Copy.Sym where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Sym.Base
open import HOTT.Copy.Base

postulate
  sym′-Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : Copy (A (δ ₀₀))} {a₀₁ : Copy (A (δ ₀₁))} (a₀₂ : Id₀₂ (λ x → Copy (A x)) δ a₀₀ a₀₁)
    {a₁₀ : Copy (A (δ ₁₀))} {a₁₁ : Copy (A (δ ₁₁))}
    (a₁₂ : Id₁₂ (λ x → Copy (A x)) δ {a₀₀} {a₀₁} a₀₂ a₁₀ a₁₁)
    (a₂₀ : Id (λ x → Copy (A x)) (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id (λ x → Copy (A x)) (δ ₂₁) a₀₁ a₁₁) →
    {δ' : el (SQ Δ)} (ϕ : δ' ≡ SYM Δ δ)
    (a₂₂ : Sq (λ x → Copy (A x)) δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁) →
    sym′ (λ x → Copy (A x)) δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ ϕ a₂₂ ↓ ≡
    {!sym′ A δ {a₀₀ ↓} {a₀₁ ↓} (a₀₂ ↓) {a₁₀ ↓} {a₁₁ ↓} {!a₁₂ ↓!} (a₂₀ ↓) (a₂₁ ↓) ϕ (a₂₂ ↓)!}
