{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Square.Equality where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base

--------------------------------------------------
-- Congruence for squares and their elements
--------------------------------------------------

Sq≡ : {Δ : Tel} (A : Δ ⇨ Type)
     {δ δ' : el (SQ Δ)} (e : δ ≡ᵉ δ')
     {a₀₀ : A ⊘ (δ ₀₀)} {a₀₀' : A ⊘ (δ' ₀₀)} (e₀₀ : a₀₀ ≡ʰ a₀₀')
     {a₀₁ : A ⊘ (δ ₀₁)} {a₀₁' : A ⊘ (δ' ₀₁)} (e₀₁ : a₀₁ ≡ʰ a₀₁')
     {a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁} {a₀₂' : Id A (δ' ₀₂) a₀₀' a₀₁'} (e₀₂ : a₀₂ ≡ʰ a₀₂')
     {a₁₀ : A ⊘ (δ ₁₀)} {a₁₀' : A ⊘ (δ' ₁₀)} (e₁₀ : a₁₀ ≡ʰ a₁₀')
     {a₁₁ : A ⊘ (δ ₁₁)} {a₁₁' : A ⊘ (δ' ₁₁)} (e₁₁ : a₁₁ ≡ʰ a₁₁')
     {a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁} {a₁₂' : Id A (δ' ₁₂) a₁₀' a₁₁'} (e₁₂ : a₁₂ ≡ʰ a₁₂')
     {a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀} {a₂₀' : Id A (δ' ₂₀) a₀₀' a₁₀'} (e₂₀ : a₂₀ ≡ʰ a₂₀')
     {a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁} {a₂₁' : Id A (δ' ₂₁) a₀₁' a₁₁'} (e₂₁ : a₂₁ ≡ʰ a₂₁') →
  Sq A δ a₀₂ a₁₂ a₂₀ a₂₁ ≡ Sq A δ' a₀₂' a₁₂' a₂₀' a₂₁'
Sq≡ A reflᵉᵉ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ reflʰ = reflᵉ
