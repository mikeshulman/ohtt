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
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
      a₂₀

fill→ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) →
  Sq A δ a₀₂ a₁₂ a₂₀ (comp→ A δ a₀₂ a₁₂ a₂₀)
fill→ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift→ {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
      a₂₀

comp← : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₂₀) a₀₀ a₁₀
comp← {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr← {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
      a₂₁

fill← : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ a₀₂ a₁₂ (comp← A δ a₀₂ a₁₂ a₂₁) a₂₁
fill← {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift← {ID Δ ▸ (λ w → A (w ₀)) ▸ (λ w → A (pop w ₁))}
      (λ w → Id′ {Δ} A (pop (pop w)) (top (pop w)) (top w))
      (δ ∷ a₀₀ ∷ a₀₁ ∷ frob₀₂ A δ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ frob₁₂ A δ a₀₂ a₁₂)
      a₂₁

-- The top-bottom fillers are then obtained from symmetry.

comp↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₁₂) a₁₀ a₁₁
comp↑ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
   coe→ (Id′≡ A (SYM₂₁ δ) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁))
        (comp→ A (SYM Δ δ)
          (coe← (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
          (coe← (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
          (coe← (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)) a₀₂)) 

fill↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ a₀₂ (comp↑ A δ a₀₂ a₂₀ a₂₁) a₂₀ a₂₁
fill↑ {Δ} A δ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
   {!-- Requires Sym.Involution and Sq≡
     sym A (SYM Δ δ)
      (coe← (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
      (coe← (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
      (coe← (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)) a₀₂)
      (comp→ A (SYM Δ δ)
          (coe← (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
          (coe← (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
          (coe← (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)) a₀₂))
      (fill→ A (SYM Δ δ)
          (coe← (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
          (coe← (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
          (coe← (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁)) a₀₂)) 
   !}

comp↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
  {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)}
  (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁) (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁) →
  Id′ A (δ ₀₂) a₀₀ a₀₁
comp↓ {Δ} A δ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
   coe→ (Id′≡ A (SYM₂₀ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁))
        (comp← A (SYM Δ δ)
          (coe← (Id′≡ A (SYM₀₂ δ) (coe←≡ʰ (cong A (SYM₀₀ δ)) a₀₀) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀)) a₂₀)
          (coe← (Id′≡ A (SYM₁₂ δ) (coe←≡ʰ (cong A (SYM₁₀ δ)) a₀₁) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₂₁)
          (coe← (Id′≡ A (SYM₂₁ δ) (coe←≡ʰ (cong A (SYM₀₁ δ)) a₁₀) (coe←≡ʰ (cong A (SYM₁₁ δ)) a₁₁)) a₁₂))

{-
fill↓ : {Δ : Tel} (A : el Δ → Type)
  {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
  {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁) (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
  Sq {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁}
    (comp↓ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁)
    {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁
fill↓ {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  sym A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁
    (comp← A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₁₂) a₁₂
    (fill← A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₁₂)
-}
