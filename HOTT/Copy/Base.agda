{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Copy.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

------------------------------
-- Copy-types
------------------------------

infixl 30 _↑
infixl 30 _↓

postulate
  Copy : Type → Type
  _↑ : {A : Type} → A → Copy A
  _↓ : {A : Type} → Copy A → A
  ↑↓ : {A : Type} (a : A) → a ↑ ↓ ≡ a

{-# REWRITE ↑↓ #-}

postulate
  Id′-Copy : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : Copy (A (δ ₀))) (a₁ : Copy (A (δ ₁))) →
    Id′ (λ w → Copy (A w)) δ a₀ a₁ ≡ Copy (Id′ A δ (a₀ ↓) (a₁ ↓))
  Id-Copy : (A : Type) (a₀ a₁ : Copy A) →
    Id (Copy A) a₀ a₁ ≡ Copy (Id A (a₀ ↓) (a₁ ↓))

{-# REWRITE Id′-Copy Id-Copy #-}

postulate
  ap↓ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a : (w : el Δ) → Copy (A w)) →
    ap (λ w → (a w) ↓) δ ≡ (ap a δ) ↓
  refl↓ : {A : Type} (a : Copy A) → refl (a ↓) ≡ refl a ↓
  -- These aren't really correct: ap↑ and refl↑ should only compute
  -- after a further ↓ has been applied.  But the same applies to
  -- ap-ap-↑ and so on.  Can we encode all of those at once in Agda?
  ap↑ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a : (w : el Δ) → A w) →
    ap (λ w → (a w) ↑) δ ≡ (ap a δ) ↑
  refl↑ : {A : Type} (a : A) → refl (a ↑) ≡ refl a ↑

{-# REWRITE ap↓ refl↓ ap↑ refl↑ #-}
