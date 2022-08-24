{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Square.Heterogeneous where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe
open import HOTT.Square.Simple
open import HOTT.Sqrt

------------------------------
-- Id-Id in the universe
------------------------------

-- This is the identity types of ≊, computed as if it were a Σ-type.
-- TODO: For some reason, defining this after declaring the rewrites
-- ＝-√ and Id-√ and dig-def causes it to spin for(ever?).
record Id≊ {A₀₀ A₀₁ : Type} (A₀₂ : A₀₀ ＝ A₀₁) {A₁₀ A₁₁ : Type} (A₁₂ : A₁₀ ＝ A₁₁)
  (A₂₀ : A₀₀ ≊ A₁₀) (A₂₁ : A₀₁ ≊ A₁₁) : Type where
  constructor Id≊[_,_,_,_,_]
  field
    ap-／ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁)
            {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
            (A₂₀ ／ a₀₀ ～ a₁₀) ＝ (A₂₁ ／ a₀₁ ～ a₁₁)
    ap-coe→ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁) →
      A₁₂ ↓ ／ coe⇒ A₂₀ ∙ a₀₀ ～ coe⇒ A₂₁ ∙ a₀₁
    ap-coe← : {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
      A₀₂ ↓ ／ coe⇐ A₂₀ ∙ a₁₀ ～ coe⇐ A₂₁ ∙ a₁₁
    ap-push→ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁) →
      ap-／ a₀₂ (ap-coe→ a₀₂) ↓ ／ push⇒ A₂₀ ∙ a₀₀ ～ push⇒ A₂₁ ∙ a₀₁
    ap-push← : {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
      ap-／ (ap-coe← a₁₂) a₁₂ ↓ ／ push⇐ A₂₀ ∙ a₁₀ ～ push⇐ A₂₁ ∙ a₁₁
open Id≊ public

postulate
  ＝-≊ : {A B : Type} (e₀ e₁ : A ≊ B) →
    (e₀ ＝ e₁) ≡ Id≊ (refl A) (refl B) e₀ e₁
  Id-≊ : {Δ : Type} (A B : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (e₀ : A δ₀ ≊ B δ₀) (e₁ : A δ₁ ≊ B δ₁) →
    Id (λ δ → A δ ≊ B δ) δ₂ e₀ e₁ ≡ Id≊ (ap A δ₂) (ap B δ₂) e₀ e₁
{-# REWRITE ＝-≊ Id-≊ #-}

-- TODO: compute ap and refl on all the constructors and fields of ≊

------------------------------
-- Heterogeneous squares
------------------------------

record ∂ʰ {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  (a₀₀ : A₀₀) (a₀₁ : A₀₁) (a₁₀ : A₁₀) (a₁₁ : A₁₁) : Typeᵉ where
  constructor ┏━_━┓_□_┗━_━┛
  infix 70 _₁₂ _₂₀ _₂₁ _₀₂
  field
    _₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁
    _₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀
    _₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁
    _₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁
open ∂ʰ public

Sqʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) → Type
Sqʰ {A₀₀} {A₀₁} {A₁₀} {A₁₁} A A₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  ap-／ {A₀₀} {A₀₁} {A ₀₂} {A₁₀} {A₁₁} {A ₁₂} {A ₂₀ ↓} {A ₂₁ ↓}
    --- Why do we need a symmetry here?
    -- TODO: This also requires (ap (λ x → kan (fst x))) and so on to
    -- compute.  We can't compute this to literally (ap kan) of
    -- fst-something, since such a rule would loop.  But maybe if we
    -- make all the higher apⁿ-kans primitive, we can compute it to
    -- the next one of fst-something.
    {!fst (ap (λ Aₓ → snd (ap kan {₁st Aₓ} {₂nd Aₓ} (₃rd' Aₓ)))
             {A₀₀ , A₀₁ , A ₀₂} {A₁₀ , A₁₁ , A ₁₂} (A ₂₀ , A ₂₁ , sym Type A A₂₂))!}
    {a₀₀} {a₀₁} (a ₀₂) {a₁₀} {a₁₁} (a ₁₂) ↓ ／ a ₂₀ ～ (a ₂₁)
