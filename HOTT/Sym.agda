{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Sym where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

--------------------
-- Symmetry
--------------------

SQ : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
  (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) → Tel
SQ Δ {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ =
  ID′ {Δ ► (λ _ → Δ)} (λ w → ID Δ (POP (λ _ → Δ) w) (TOP (λ _ → Δ) w))
    {PAIR (λ _ → Δ) δ₀₀ δ₁₀} {PAIR (λ _ → Δ) δ₀₁ δ₁₁}
    (PAIR (λ w₂ → ID′ {Δ} (λ _ → Δ) w₂ δ₁₀ δ₁₁) δ₀₂ δ₁₂)
    δ₂₀ δ₂₁

postulate
  SYM : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
    (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) →
    el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁) → el (SQ Δ δ₂₀ δ₂₁ δ₀₂ δ₁₂)
  SYM-SYM : (Δ : Tel) {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
    (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁)) →
    SYM Δ δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) ≡ δ₂₂

{-# REWRITE SYM-SYM #-}

Sq : {Δ : Tel} (A : el Δ → Type)
     {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
     (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
     {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
     (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) → Type
Sq {Δ} A {δ₀₀} {δ₀₁} δ₀₂ {δ₁₀} {δ₁₁} δ₁₂ δ₂₀ δ₂₁ δ₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id′ {Δ ► (λ _ → Δ)
          ► (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁))
          ▸ (λ w₀w₁w₂ → A (POP (λ _ → Δ) (POP (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) w₀w₁w₂)))
          ▸ (λ w₀w₁w₂a₀ → A (TOP (λ _ → Δ) (POP (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) (pop w₀w₁w₂a₀))))}
       (λ w₀w₁w₂a₀a₁ → Id′ {Δ} A (TOP (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) (pop (pop w₀w₁w₂a₀a₁)))
                           (top (pop w₀w₁w₂a₀a₁)) (top w₀w₁w₂a₀a₁))
       {PAIR (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) (PAIR (λ _ → Δ) δ₀₀ δ₁₀) δ₂₀ ∷ a₀₀ ∷ a₁₀}
       {PAIR (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) (PAIR (λ _ → Δ) δ₀₁ δ₁₁) δ₂₁ ∷ a₀₁ ∷ a₁₁}
       (PAIR (λ w₀₂w₁₂ → SQ Δ (POP (λ _ → ID Δ δ₁₀ δ₁₁) w₀₂w₁₂) (TOP (λ _ → ID Δ δ₁₀ δ₁₁) w₀₂w₁₂) δ₂₀ δ₂₁)
         (PAIR (λ _ → ID Δ δ₁₀ δ₁₁) δ₀₂ δ₁₂) δ₂₂ ∷
         coe→ (Id-AP (λ w → (POP (λ _ → Δ) (POP (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) w)))
                     {PAIR {Δ ► (λ _ → Δ)} (λ w₀w₁ → ID Δ (POP {Δ} (λ _ → Δ) w₀w₁) (TOP {Δ} (λ _ → Δ) w₀w₁))
                           (PAIR {Δ} (λ _ → Δ) δ₀₀ δ₁₀) δ₂₀}
                     {PAIR {Δ ► (λ _ → Δ)} (λ w₀w₁ → ID Δ (POP {Δ} (λ _ → Δ) w₀w₁) (TOP {Δ} (λ _ → Δ) w₀w₁))
                           (PAIR {Δ} (λ _ → Δ) δ₀₁ δ₁₁) δ₂₁}
                     (PAIR (λ w₀₂w₁₂ → SQ Δ (POP (λ _ → ID Δ δ₁₀ δ₁₁) w₀₂w₁₂) (TOP (λ _ → ID Δ δ₁₀ δ₁₁) w₀₂w₁₂) δ₂₀ δ₂₁)
                           (PAIR (λ _ → ID Δ δ₁₀ δ₁₁) δ₀₂ δ₁₂) δ₂₂)
                     A a₀₀ a₀₁)
              a₀₂ ∷
         coe→ (Id-AP (λ z → TOP (λ _ → Δ) (POP (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) (pop z)))
                 {PAIR (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) (PAIR (λ _ → Δ) δ₀₀ δ₁₀) δ₂₀ ∷ a₀₀}
                 {PAIR (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) (PAIR (λ _ → Δ) δ₀₁ δ₁₁) δ₂₁ ∷ a₀₁}
                 (PAIR (λ w₀₂w₁₂ → SQ Δ (POP (λ _ → ID Δ δ₁₀ δ₁₁) w₀₂w₁₂) (TOP (λ _ → ID Δ δ₁₀ δ₁₁) w₀₂w₁₂) δ₂₀ δ₂₁)
                   (PAIR (λ _ → ID Δ δ₁₀ δ₁₁) δ₀₂ δ₁₂) δ₂₂ ∷
                   coe→ (Id-AP (λ w → POP (λ _ → Δ) (POP (λ w₀w₁ → ID Δ (POP (λ _ → Δ) w₀w₁) (TOP (λ _ → Δ) w₀w₁)) w))
                          (PAIR (λ w₀₂w₁₂ → SQ Δ (POP (λ _ → ID Δ δ₁₀ δ₁₁) w₀₂w₁₂) (TOP (λ _ → ID Δ δ₁₀ δ₁₁) w₀₂w₁₂) δ₂₀ δ₂₁)
                            (PAIR (λ _ → ID Δ δ₁₀ δ₁₁) δ₀₂ δ₁₂) δ₂₂) A a₀₀ a₀₁)
                   a₀₂) A a₁₀ a₁₁)
         a₁₂)
       a₂₀ a₂₁

postulate
  sym : {Δ : Tel} (A : el Δ → Type)
        {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
        (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
        {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
        (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) →
        Sq A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁ → Sq A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂ a₁₂
  sym-sym : {Δ : Tel} (A : el Δ → Type)
            {δ₀₀ δ₀₁ : el Δ} (δ₀₂ : el (ID Δ δ₀₀ δ₀₁)) {δ₁₀ δ₁₁ : el Δ} (δ₁₂ : el (ID Δ δ₁₀ δ₁₁))
            (δ₂₀ : el (ID Δ δ₀₀ δ₁₀)) (δ₂₁ : el (ID Δ δ₀₁ δ₁₁)) (δ₂₂ : el (SQ Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁))
            {a₀₀ : A δ₀₀} {a₀₁ : A δ₀₁} (a₀₂ : Id′ A δ₀₂ a₀₀ a₀₁) {a₁₀ : A δ₁₀} {a₁₁ : A δ₁₁} (a₁₂ : Id′ A δ₁₂ a₁₀ a₁₁)
            (a₂₀ : Id′ A δ₂₀ a₀₀ a₁₀) (a₂₁ : Id′ A δ₂₁ a₀₁ a₁₁) (a₂₂ : Sq A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁) →
            sym A δ₂₀ δ₂₁ δ₀₂ δ₁₂ (SYM Δ δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂) a₂₀ a₂₁ a₀₂ a₁₂ (sym A δ₀₂ δ₁₂ δ₂₀ δ₂₁ δ₂₂ a₀₂ a₁₂ a₂₀ a₂₁ a₂₂) ≡ a₂₂

{-# REWRITE sym-sym #-}
