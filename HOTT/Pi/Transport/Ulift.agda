{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Pi.Transport.Ulift where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Pi.Transport.Utr

postulate
  ulift→Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₀ : Π (A (δ ₀)) (B (δ ₀))) (u₁ u₁' : Π (A (δ ₁)) (B (δ ₁)))
    (u₂ : Id′ (λ w → Π (A w) (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → Π (A w) (B w)) δ u₀ u₁') →
    ulift→      (λ w → Π (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-ulift→ (λ w → Π (A w) (B w)) δ u₀ u₁ u₁' u₂ u₂'
  ulift←Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (u₁ : Π (A (δ ₁)) (B (δ ₁))) (u₀ u₀' : Π (A (δ ₀)) (B (δ ₀)))
    (u₂ : Id′ (λ w → Π (A w) (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → Π (A w) (B w)) δ u₀' u₁) →
    ulift←      (λ w → Π (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-ulift← (λ w → Π (A w) (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE ulift→Π ulift←Π #-}
