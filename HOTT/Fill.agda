{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Fill where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Sym.Base

------------------------------
-- Composition and filling
------------------------------

-- Left-right and right-left fillers come from transport and lifting over squares.

comp→ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) →
  Id′ A (δ ₂₁) a₀₁ a₁₁
comp→ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  tr→ {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂)
      a₂₀

fill→ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) →
  Sq A δ a₀₂ (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂) a₂₀ (comp→ A δ a₀₂ a₁₂ a₂₀)
fill→ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift→ {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂)
      a₂₀

comp← : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₂₀) a₀₀ a₁₀
comp← {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr← {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂)
      a₂₁

fill← : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ a₀₂ (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂) (comp← A δ a₀₂ a₁₂ a₂₁) a₂₁
fill← {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift← {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ a₁₂)
      a₂₁

-- The top-bottom fillers are then obtained from symmetry.

comp↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₁₂) a₁₀ a₁₁
comp↑ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ = comp→ A (SYM Δ δ) a₂₀ a₂₁ a₀₂

fill↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ a₀₂ (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} a₀₂ (comp↑ A δ a₀₂ a₂₀ a₂₁)) a₂₀ a₂₁
fill↑ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
   sym A (SYM Δ δ)
     {a₀₀} {a₁₀} a₂₀
     {a₀₁} {a₁₁} (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (SYM Δ δ) a₂₀ a₂₁)
     a₀₂
     (comp→ A (SYM Δ δ) a₂₀ a₂₁ a₀₂)
     (fill→ A (SYM Δ δ) a₂₀ a₂₁ a₀₂)

comp↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)}
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
  (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₀₂) a₀₀ a₀₁
comp↓ {Δ} A δ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ = comp← A (SYM Δ δ) a₂₀ a₂₁ a₁₂

fill↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)}
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
  (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ (comp↓ A δ a₁₂ a₂₀ a₂₁) (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) δ {a₀₀} {a₀₁} (comp↓ A δ a₁₂ a₂₀ a₂₁) a₁₂) a₂₀ a₂₁
fill↓ {Δ} A δ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
   sym A (SYM Δ δ)
     {a₀₀} {a₁₀} a₂₀
     {a₀₁} {a₁₁} (Id′-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (SYM Δ δ) a₂₀ a₂₁)
     (comp← A (SYM Δ δ) a₂₀ a₂₁ a₁₂)
     a₁₂
     (fill← A (SYM Δ δ) a₂₀ a₂₁ a₁₂)
