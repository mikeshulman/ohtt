module HOTT.Square.Heterogeneous.Base where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe.Parametric
open import HOTT.Functoriality
open import HOTT.Square.Simple
open import HOTT.IdCube
open import HOTT.Corr

----------------------------------------
-- Heterogeneous squares
----------------------------------------

record ∂2ʰ {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  (a₀₀ : A₀₀) (a₀₁ : A₀₁) (a₁₀ : A₁₀) (a₁₁ : A₁₁) : Typeᵉ where
  constructor ┏━_━┓_□_┗━_━┛
  infix 70 _₁₂ _₂₀ _₂₁ _₀₂
  field
    _₁₂ : ⟦ A ₁₂ ⟧ ∙ a₁₀ ∙ a₁₁
    _₂₀ : ⟦ A ₂₀ ⟧ ∙ a₀₀ ∙ a₁₀
    _₂₁ : ⟦ A ₂₁ ⟧ ∙ a₀₁ ∙ a₁₁
    _₀₂ : ⟦ A ₀₂ ⟧ ∙ a₀₀ ∙ a₀₁
open ∂2ʰ public

sym-∂2ʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} {A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁} {A₂₂ : Sq Type A}
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} →
  ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁ → ∂2ʰ (sym-∂2 A) (sym Type A A₂₂) a₀₀ a₁₀ a₀₁ a₁₁
sym-∂2ʰ a = ┏━   a ₂₁   ━┓
            a ₀₂  □   a ₁₂
            ┗━   a ₂₀   ━┛

∂2ʰ-refl-refl : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} →
  ∂2ʰ (refl-∂2 A) (refl (refl A)) a₀₀ a₀₁ a₁₀ a₁₁ → ∂2 A a₀₀ a₀₁ a₁₀ a₁₁
∂2ʰ-refl-refl ┏━ a₁₂ ━┓
              a₂₀ □ a₂₁
              ┗━ a₀₂ ━┛ = ┌─  a₁₂  ─┐
                           a₂₀  □  a₂₁
                           └─  a₀₂  ─┘

Sqʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) → Type
Sqʰ {A₀₀} {A₀₁} {A₁₀} {A₁₁} A A₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  ⟦ _∙_ {（ x₀ ⦂ A₁₀ ）× （ x₁ ⦂ A₁₁ ）× ⟦ A ₁₂ ⟧ ∙ x₀ ∙ x₁}
    (_∙_ {（ x₀ ⦂ A₀₀ ）× （ x₁ ⦂ A₀₁ ）× ⟦ A ₀₂ ⟧ ∙ x₀ ∙ x₁}
      (snd (fst (corr {𝐬 (𝐬 𝐳)} (((★ , ★ , ★ , A₀₀ , A₁₀) , (★ , ★ , ★ , A₀₁ , A₁₁) , (★ , ★ , ★ , A ₀₂ , A ₁₂) , A ₂₀ , A ₂₁) , A₂₂))))
     -- I don't know why the families aren't inferred here.
       (a₀₀ , a₀₁ , a ₀₂))
    (a₁₀ , a₁₁ , a ₁₂) ⟧ ∙ (a ₂₀) ∙ (a ₂₁)

-- The other component of corr is a primitive symmetrized square.  The
-- two are interchanged by symmetry acting on U, and are isomorphic to
-- each other by a postulated heterogeneous symmetry.
Symʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂2 Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂2ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) → Type
Symʰ {A₀₀} {A₀₁} {A₁₀} {A₁₁} A A₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  ⟦ _∙_ {（ x₀ ⦂ A₀₁ ）× （ x₁ ⦂ A₁₁ ）× ⟦ A ₂₁ ⟧ ∙ x₀ ∙ x₁}
    (_∙_ {（ x₀ ⦂ A₀₀ ）× （ x₁ ⦂ A₁₀ ）× ⟦ A ₂₀ ⟧ ∙ x₀ ∙ x₁}
      (snd (corr {𝐬 (𝐬 𝐳)} (((★ , ★ , ★ , A₀₀ , A₁₀) , (★ , ★ , ★ , A₀₁ , A₁₁) , (★ , ★ , ★ , A ₀₂ , A ₁₂) , A ₂₀ , A ₂₁) , A₂₂)))
      (a₀₀ , a₁₀ , a ₂₀))
    (a₀₁ , a₁₁ , a ₂₁) ⟧ ∙ (a ₀₂) ∙ (a ₁₂)
