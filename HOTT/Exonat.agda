{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Exonat where

open import HOTT.Base

data ℕᵉ : Typeᵉ where
  𝐳 : ℕᵉ
  𝐬 : ℕᵉ → ℕᵉ
