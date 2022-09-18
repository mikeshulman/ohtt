module HOTT.Square.Heterogeneous.LeftRight where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe
open import HOTT.Square.Simple
open import HOTT.Exonat
open import HOTT.Square.Heterogeneous.Base

--------------------------------------------------
-- Heterogeneous composition and filling
--------------------------------------------------

IDʰ : Type
IDʰ = （ A₀ ⦂ Type ）× （ A₁ ⦂ Type ）× （ A₂ ⦂ A₀ ＝ A₁ ）× A₀ × A₁

Idʰ : IDʰ → Type
Idʰ A = ₃rd A ↓ ／ ₄th A ～ ₅th' A

module _  {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} where

  compʰ→ : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) →
    A ₂₁ ↓ ／ a₀₁ ～ a₁₁
  compʰ→ a₀₂ a₁₂ a₂₀ = tr⇒ Idʰ {A₀₀ , A₁₀ , A ₂₀ , a₀₀ , a₁₀} {A₀₁ , A₁₁ , A ₂₁ , a₀₁ , a₁₁} (A ₀₂ , A ₁₂ , A₂₂ , a₀₂ , a₁₂) ∙ a₂₀

  fillʰ→ : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) →
    Sqʰ A A₂₂ ┏━   a₁₂   ━┓
              a₂₀  □   compʰ→ a₀₂ a₁₂ a₂₀
              ┗━   a₀₂   ━┛
  fillʰ→ a₀₂ a₁₂ a₂₀ = lift⇒ Idʰ {A₀₀ , A₁₀ , A ₂₀ , a₀₀ , a₁₀} {A₀₁ , A₁₁ , A ₂₁ , a₀₁ , a₁₁} (A ₀₂ , A ₁₂ , A₂₂ , a₀₂ , a₁₂) ∙ a₂₀

  compʰ← : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    A ₂₀ ↓ ／ a₀₀ ～ a₁₀
  compʰ← a₀₂ a₁₂ a₂₁ = tr⇐ Idʰ {A₀₀ , A₁₀ , A ₂₀ , a₀₀ , a₁₀} {A₀₁ , A₁₁ , A ₂₁ , a₀₁ , a₁₁} (A ₀₂ , A ₁₂ , A₂₂ , a₀₂ , a₁₂) ∙ a₂₁

  fillʰ← : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    Sqʰ A A₂₂ ┏━                 a₁₂   ━┓
              compʰ← a₀₂ a₁₂ a₂₁  □    a₂₁
              ┗━                 a₀₂   ━┛
  fillʰ← a₀₂ a₁₂ a₂₁ = lift⇐ Idʰ {A₀₀ , A₁₀ , A ₂₀ , a₀₀ , a₁₀} {A₀₁ , A₁₁ , A ₂₁ , a₀₁ , a₁₁} (A ₀₂ , A ₁₂ , A₂₂ , a₀₂ , a₁₂) ∙ a₂₁
