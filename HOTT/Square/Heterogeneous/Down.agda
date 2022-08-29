{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Square.Heterogeneous.Down where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe
open import HOTT.Square.Simple
open import HOTT.Exonat
open import HOTT.Square.Heterogeneous.Base
open import HOTT.Square.Heterogeneous.Sym
--open import HOTT.Square.Heterogeneous.LeftRight

module _  {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} where

  compʰ↓ : (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
     A ₀₂ ↓ ／ a₀₀ ～ a₀₁
  compʰ↓ a₁₂ a₂₀ a₂₁ = coe⇐ (ap-／ (snd (kan {𝐬 (𝐬 𝐳)} ((A₀₀ , A₁₀ , A ₂₀) , (A₀₁ , A₁₁ , A ₂₁) , (A ₀₂ , A ₁₂ , A₂₂)))) a₂₀ a₂₁ ↓) ∙ a₁₂

  fillʰ↓ : (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    Sqʰ A A₂₂ ┏━         a₁₂           ━┓
              a₂₀         □           a₂₁
              ┗━  compʰ↓ a₁₂ a₂₀ a₂₁   ━┛
  fillʰ↓ a₁₂ a₂₀ a₂₁ =
    unsymʰ A A₂₂ ┏━         a₁₂          ━┓
                 a₂₀         □          a₂₁
                 ┗━  compʰ↓ a₁₂ a₂₀ a₂₁  ━┛
           (push⇐ (ap-／ (snd (kan {𝐬 (𝐬 𝐳)} ((A₀₀ , A₁₀ , A ₂₀) , (A₀₁ , A₁₁ , A ₂₁) , (A ₀₂ , A ₁₂ , A₂₂)))) a₂₀ a₂₁ ↓) ∙ a₁₂)
