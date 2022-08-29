{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Square.Heterogeneous.Sym where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe
open import HOTT.Square.Simple
open import HOTT.Square.Heterogeneous.Base

------------------------------
-- Heterogeneous symmetry
------------------------------

postulate
  symʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) →
    Sqʰ A A₂₂ a → Symʰ A A₂₂ a
  unsymʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) →
    Symʰ A A₂₂ a → Sqʰ A A₂₂ a
postulate
  unsym-symʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sqʰ A A₂₂ a) →
    unsymʰ A A₂₂ a (symʰ A A₂₂ a a₂₂) ≡ a₂₂
  sym-unsymʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Symʰ A A₂₂ a) →
    symʰ A A₂₂ a (unsymʰ A A₂₂ a a₂₂) ≡ a₂₂
{-# REWRITE unsym-symʰ sym-unsymʰ #-}

-- TODO: symʰ computes on ap to symᵈ, and on refl to sym.

