{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Types.Universe where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Telescope
open import HOTT.Types.Pi

----------------------------------------
-- Identity types of the universe
----------------------------------------

-- Dependent identity types
Id : {A : Type} (B : A ⇒ Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B ∙ a₀) (b₁ : B ∙ a₁) → Type

record _＝U_ (A B : Type) : Type where
  no-eta-equality
  field
    _//_~_ : (a : A) (b : B) → Type
    tr→ : A → B
    lift→ : (a : A) → _//_~_ a (tr→ a)
    tr← : B → A
    lift← : (b : B) → _//_~_ (tr← b) b
    utr→ : (a : A) (b₀ b₁ : B) (r₀ : _//_~_ a b₀) (r₁ : _//_~_ a b₁) → b₀ ＝ b₁
    ulift→ : (a : A) (b₀ b₁ : B) (r₀ : _//_~_ a b₀) (r₁ : _//_~_ a b₁) → Id (ƛ b ⇒ _//_~_ a b) (utr→ a b₀ b₁ r₀ r₁) r₀ r₁
    utr← : (b : B) (a₀ a₁ : A) (r₀ : _//_~_ a₀ b) (r₁ : _//_~_ a₁ b) → a₀ ＝ a₁
    ulift← : (b : B) (a₀ a₁ : A) (r₀ : _//_~_ a₀ b) (r₁ : _//_~_ a₁ b) → Id (ƛ a ⇒ _//_~_ a b) (utr← b a₀ a₁ r₀ r₁) r₀ r₁

open _＝U_ public

postulate
  ＝-U : (A B : Type) → (A ＝ B) ≡ (A ＝U B)

{-# REWRITE ＝-U #-}

postulate
  refl//~ : (A : Type) (a₀ a₁ : A) → (refl A // a₀ ~ a₁) ≡ (a₀ ＝ a₁)

{-# REWRITE refl//~ #-}

----------------------------------------
-- Dependent identity types
----------------------------------------

-- Now we can define these
Id B {a₀} {a₁} a₂ b₀ b₁ = refl B ∙ a₀ ∙ a₁ ∙ a₂ // b₀ ~ b₁

-- We also have ones dependent on a telescope
𝕀𝕕 : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₀ : A ⊘ δ ₀) (a₁ : A ⊘ δ ₁) → Type
𝕀𝕕 {Δ} A δ a₀ a₁ = refl A ⊘ δ // a₀ ~ a₁
