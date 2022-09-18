module HOTT.Square.Heterogeneous.Up where

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

  compʰ↑ : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    A ₁₂ ↓ ／ a₁₀ ～ a₁₁
  compʰ↑ a₀₂ a₂₀ a₂₁ =
    -- The obvious (compʰ→ (sym-∂ A) (sym Type A A₂₂) a₂₀ a₂₁ a₀₂)
    -- will reduce to this once we define sym on the universe (which
    -- means defining the action of kan on sym).  For now we give the
    -- explicit version, which is the one that allows us to define
    -- fillʰ↑.
    coe⇒ (ap-／ (snd (kan {𝐬 (𝐬 𝐳)} ((A₀₀ , A₁₀ , A ₂₀) , (A₀₁ , A₁₁ , A ₂₁) , (A ₀₂ , A ₁₂ , A₂₂)))) a₂₀ a₂₁ ↓) ∙ a₀₂

  fillʰ↑ : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    Sqʰ A A₂₂ ┏━  compʰ↑ a₀₂ a₂₀ a₂₁   ━┓
              a₂₀         □           a₂₁
              ┗━         a₀₂          ━┛
  fillʰ↑ a₀₂ a₂₀ a₂₁ =
    unsymʰ A A₂₂ ┏━  compʰ↑ a₀₂ a₂₀ a₂₁  ━┓
                 a₂₀         □          a₂₁
                 ┗━         a₀₂          ━┛
           (push⇒ (ap-／ (snd (kan {𝐬 (𝐬 𝐳)} ((A₀₀ , A₁₀ , A ₂₀) , (A₀₁ , A₁₁ , A ₂₁) , (A ₀₂ , A ₁₂ , A₂₂)))) a₂₀ a₂₁ ↓) ∙ a₀₂) 
