{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.ApRefl where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square
open import HOTT.Sym

{-
postulate
  AP-REFL≡SYM-REFL : (Γ Δ : Tel) (f : el Γ → el Δ) (γ : el (ID Γ)) →
    AP (λ x → REFL (f x)) γ ≡ SYM Δ (REFL (AP f γ))

{-# REWRITE AP-REFL≡SYM-REFL #-}
-}

{- Unported
postulate
  ap-refl : {Δ : Tel} {A : el Δ → Type} (f : (x : el Δ) → A x)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ} (λ w → refl (f w)) {δ₀} {δ₁} δ₂ ≡
    {!sym A (REFL δ₀) (REFL δ₁) δ₂ δ₂ (DEGSQ-LR Δ δ₂) (refl (f δ₀)) (refl (f δ₁)) (ap f δ₂) (ap f δ₂)!}
-}
