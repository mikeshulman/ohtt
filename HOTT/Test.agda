{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Test where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

----------------------------------------
-- Examples for testing
----------------------------------------

postulate
  A : Type
  a₀ a₁ : A
  a₂ : Id A a₀ a₁

A′ : el ε → Type
A′ _ = A

postulate
  B : el (ε ▸ A′) → Type
  b₀ : B ([] ∷ a₀)
  b₁ : B ([] ∷ a₁)
  b₂ : Id′ B ([] ∷ a₂) b₀ b₁
  C : el (ε ▸ A′ ▸ B) → Type
  c₀ : C ([] ∷ a₀ ∷ b₀)
  c₁ : C ([] ∷ a₁ ∷ b₁)
  c₂ : Id′ C ([] ∷ a₂ ∷ b₂) c₀ c₁

-- Testing normalization of ap-top (normalize these with C-c C-n).
-- Observe that the results involve coercions along Id-AP but we can
-- hope that for concrete types these will compute away.  In
-- particular, with Id-AP-const, the coercions already vanish for the
-- "-A" versions.
egA-A = ap {Δ = ε ▸ A′} (λ w → top w) {[] ∷ a₀} {[] ∷ a₁} ([] ∷ a₂)
egAB-B = ap {Δ = ε ▸ A′ ▸ B} (λ w → top w) {[] ∷ a₀ ∷ b₀} {[] ∷ a₁ ∷ b₁} ([] ∷ a₂ ∷ b₂)
egAB-A = ap {Δ = ε ▸ A′ ▸ B} (λ w → top (pop w)) {[] ∷ a₀ ∷ b₀} {[] ∷ a₁ ∷ b₁} ([] ∷ a₂ ∷ b₂)
egABC-C = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top w) {[] ∷ a₀ ∷ b₀ ∷ c₀} {[] ∷ a₁ ∷ b₁ ∷ c₁} ([] ∷ a₂ ∷ b₂ ∷ c₂)
egABC-B = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top (pop w)) {[] ∷ a₀ ∷ b₀ ∷ c₀} {[] ∷ a₁ ∷ b₁ ∷ c₁} ([] ∷ a₂ ∷ b₂ ∷ c₂)
egABC-A = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top (pop (pop w))) {[] ∷ a₀ ∷ b₀ ∷ c₀} {[] ∷ a₁ ∷ b₁ ∷ c₁} ([] ∷ a₂ ∷ b₂ ∷ c₂)

-- TODO: Something's wrong; egAB-A and egABC-A aren't reducing away
-- their top-pop-s of lists.  It looks like maybe the type of the pop
-- doesn't match the type of the _∷_.  How can that be?

-- neweg = top {ε} {λ t₂ → Id A a₀ a₁}
--  (pop {ε ▸ (λ t₂ → Id A a₀ a₁)}
--  {λ t₂ →
--     Id′ {ε ▸ (λ _ → A) ▸ B ▸ (λ w → A)}
--     (λ w →
--        B (_∷_ {ε} {λ _ → A} [] (top {ε ▸ (λ _ → A) ▸ B} {λ w₁ → A} w)))
--     {_∷_ {ε ▸ (λ _ → A) ▸ B} {λ w → A}
--      (_∷_ {ε ▸ (λ _ → A)} {B} (_∷_ {ε} {λ _ → A} [] a₀) b₀) a₀}
--     {_∷_ {ε ▸ (λ _ → A) ▸ B} {λ w → A}
--      (_∷_ {ε ▸ (λ _ → A)} {B} (_∷_ {ε} {λ _ → A} [] a₁) b₁) a₁}
--     (_∷_
--      {ε ▸ (λ δ₂ → Id A a₀ a₁) ▸
--       (λ δ₂ →
--          Id′ {ε ▸ (λ _ → A)} B {_∷_ {ε} {λ _ → A} [] a₀}
--          {_∷_ {ε} {λ _ → A} [] a₁} δ₂ b₀ b₁)}
--      {λ w → Id A a₀ a₁}
--      (_∷_ {ε ▸ (λ δ₂ → Id A a₀ a₁)}
--       {λ δ₂ →
--          Id′ {ε ▸ (λ _ → A)} B {_∷_ {ε} {λ _ → A} [] a₀}
--          {_∷_ {ε} {λ _ → A} [] a₁} δ₂ b₀ b₁}
--       (_∷_ {ε} {λ δ₂ → Id A a₀ a₁} [] a₂) b₂)
--      (top {ε} {λ _ → Id A a₀ a₁} t₂))
--     b₀ b₁}
--  (_∷_ {ε ▸ (λ δ₂ → Id A a₀ a₁)}
--   {λ δ₂ →
--      Id′ {ε ▸ (λ _ → A)} B {_∷_ {ε} {λ _ → A} [] a₀}
--      {_∷_ {ε} {λ _ → A} [] a₁} δ₂ b₀ b₁}
--   (_∷_ {ε} {λ δ₂ → Id A a₀ a₁} [] a₂) b₂))
  
eg₁ = ap-top {ε ▸ A′ ▸ B} (λ _ → ε) (λ _ → A′) (λ w → pop w) ([] ∷ a₀ ∷ b₀) ([] ∷ a₁ ∷ b₁) ([] ∷ a₂ ∷ b₂)
eg₂ = AP-pop {ε ▸ A′ ▸ B} {ε ▸ A′} B (λ w → w) {[] ∷ a₀ ∷ b₀} {[] ∷ a₁ ∷ b₁} ([] ∷ a₂ ∷ b₂)
-- It looks like the problem is with AP′-pop:
eg₃ = AP′-pop {ε ▸ A′ ▸ B} {λ _ → ε ▸ A′} (λ _ → B) (λ w → w) {[] ∷ a₀ ∷ b₀} {[] ∷ a₁ ∷ b₁} ([] ∷ a₂ ∷ b₂)
