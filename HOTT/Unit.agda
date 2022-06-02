{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Unit where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

--------------------
-- Unit type
--------------------

record ⊤ : Type where
  constructor ★

-- The rule for Id′ follows from this one together with Id′-const.
postulate
  Id⊤ : (u v : ⊤) → Id ⊤ u v ≡ ⊤

{-# REWRITE Id⊤ #-}

-- Similarly, the rule for general ap follows from this one together with ap-const.
postulate
  refl★ : refl ★ ≡ ★

{-# REWRITE refl★ #-}

----------------------------------------
-- Transport in the unit type
----------------------------------------

postulate
  tr→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤) → tr→ {Δ} (λ _ → ⊤) δ₂ a₀ ≡ a₀
  lift→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤) → lift→ {Δ} (λ _ → ⊤) δ₂ a₀ ≡ ★
  tr←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤) → tr← {Δ} (λ _ → ⊤) δ₂ a₁ ≡ a₁
  lift←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤) → lift← {Δ} (λ _ → ⊤) δ₂ a₁ ≡ ★
  utr→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤)
    (a₁ a₁' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁') →
    utr→ {Δ} (λ _ → ⊤) δ₂ a₀ a₁ a₁' a₂ a₂' ≡ ★
  ulift→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤)
    (a₁ a₁' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁') →
    ulift→ {Δ} (λ _ → ⊤) δ₂ a₀ a₁ a₁' a₂ a₂' ≡ ★
  utr←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤)
    (a₀ a₀' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀' a₁) →
    utr← {Δ} (λ _ → ⊤) δ₂ a₁ a₀ a₀' a₂ a₂' ≡ ★
  ulift←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤)
    (a₀ a₀' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀' a₁) →
    ulift← {Δ} (λ _ → ⊤) δ₂ a₁ a₀ a₀' a₂ a₂' ≡ ★

{-# REWRITE tr→⊤ lift→⊤ tr←⊤ lift←⊤ utr→⊤ ulift→⊤ utr←⊤ ulift←⊤ #-}
