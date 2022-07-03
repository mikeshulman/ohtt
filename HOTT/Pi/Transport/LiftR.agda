{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --experimental-lossy-unification #-}

module HOTT.Pi.Transport.LiftR where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Square.Extended
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Pi.Transport.Tr

module Lift→Π {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
  (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (B (δ ₀)))
  (a₀ : A (δ ₀)) (a₁ : A (δ ₁)) (a₂ : Id (Λ⇨ A) δ a₀ a₁) where

  the-Δ : Tel
  the-Δ = Δ ▸ Λ⇨ A

  the-A : (Δ ▸ Λ⇨ A) ⇨ Type
  the-A = Λ⇨ (uncurry {A = Λ⇨ A} B)

  the-δ : el (ID▸▸ (Id/ (Λ⇨ A)) ▸ Id/ (Id/ (Λ⇨ A)))
  the-δ = sq∷ (Λ⇨ A) (DEGSQ-LR δ)
    {a₀} {tr← (Λ⇨ A) δ a₁}
    (utr← (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁))
    {a₁} {a₁} (refl a₁) a₂ (lift← (Λ⇨ A) δ a₁)
    (ulift←sq (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁))

  the-a₀₀ : uncurry B (the-δ ₀₀)
  the-a₀₀ = f₀ ∙ a₀

  the-a₀₁ : uncurry B (the-δ ₀₁)
  the-a₀₁ = f₀ ∙ tr← (Λ⇨ A) δ a₁

  the-a₀₂ : Id (Λ⇨ (uncurry B)) (the-δ ₀₂) the-a₀₀ the-a₀₁
  the-a₀₂ = coe→ (Id-AP {ε▸ (A (δ ₀))} (λ x → δ ₀ ∷ top x)
                    ([] ∷ a₀ ∷ tr← (Λ⇨ A) δ a₁ ∷
                      utr← (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁))
                    (Λ⇨ (uncurry {A = Λ⇨ A} B))
                    (f₀ ∙ a₀) (f₀ ∙ tr← (Λ⇨ A) δ a₁))
            (refl f₀ ∙ a₀ ∙ (tr← (Λ⇨ A) δ a₁) ∙
              (utr← (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁)))

  the-a₁₀ : uncurry B (the-δ ₁₀)
  the-a₁₀ = tr→ (Λ⇨ (uncurry {A = Λ⇨ A} B))
                (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁)
                (f₀ ∙ tr← (Λ⇨ A) δ a₁)

  the-a₁₁ : uncurry B (the-δ ₁₁)
  the-a₁₁ = the-a₁₀

  the-a₁₂ : Id (Λ⇨ (uncurry B)) (the-δ ₁₂) the-a₁₀ the-a₁₁
  the-a₁₂ = refl the-a₁₀

  the-a₂₁ : Id (Λ⇨ (uncurry B)) (the-δ ₂₁) the-a₀₁ the-a₁₁
  the-a₂₁ = lift→ (Λ⇨ (uncurry {A = Λ⇨ A} B))
                  (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁)
                  (f₀ ∙ tr← (Λ⇨ A) δ a₁)

  -- It seems like we can't write
  --- Id (Λ⇨ (uncurry B)) (the-δ ₂₀) the-a₀₀ the-a₁₀
  -- here, or else it won't have the correct type outside the module.
  -- I'm not really sure why that is.
  the-lift→ : Id (Λ⇨ (uncurry B)) (δ ∷ a₀ ∷ a₁ ∷ a₂)
    (f₀ ∙ a₀)
    (tr→ (Λ⇨ (uncurry B))
         (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁)
         (f₀ ∙ tr← (Λ⇨ A) δ a₁))
  the-lift→ = comp← {Δ = the-Δ} the-A the-δ
    {the-a₀₀} {the-a₀₁} the-a₀₂ {the-a₁₀} {the-a₁₁} the-a₁₂ the-a₂₁

postulate
  lift→Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (B (δ ₀))) →
    lift→ (Λ w ⇨ Π (A w) (B w)) δ f₀ ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ (Lift→Π.the-lift→ A B δ f₀ a₀ a₁ a₂)

{-# REWRITE lift→Π #-}
