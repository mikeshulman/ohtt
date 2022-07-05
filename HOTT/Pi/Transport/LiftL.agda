{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --experimental-lossy-unification #-}

module HOTT.Pi.Transport.LiftL where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Uncoerce
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Pi.Transport.Tr

module Lift←Π {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
  (δ : el (ID Δ)) (f₁ : Π (A (δ ₁)) (B (δ ₁)))
  (a₀ : A (δ ₀)) (a₁ : A (δ ₁)) (a₂ : Id (Λ⇨ A) δ a₀ a₁) where

  the-Δ : Tel
  the-Δ = Δ ▸ Λ⇨ A

  the-A : (Δ ▸ Λ⇨ A) ⇨ Type
  the-A = Λ⇨ (uncurry {A = Λ⇨ A} B)

  the-δ : el (ID▸▸ (Id/ (Λ⇨ A)) ▸ Id/ (Id/ (Λ⇨ A)))
  the-δ = sq∷ (Λ⇨ A) (DEGSQ-LR δ)
    {a₀} {a₀} (refl a₀)
    {a₁} {tr→ (Λ⇨ A) δ a₀}
    (utr→ (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀))
    a₂ (lift→ (Λ⇨ A) δ a₀)
    (ulift→sq (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀))

  the-a₀₀ : uncurry B (the-δ ₀₀)
  the-a₀₀ = tr← (Λ⇨ (uncurry {A = Λ⇨ A} B))
                (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
                (f₁ ∙ tr→ (Λ⇨ A) δ a₀)

  the-a₀₁ : uncurry B (the-δ ₀₁)
  the-a₀₁ = the-a₀₀

  the-a₀₂ : Id (Λ⇨ (uncurry B)) (the-δ ₀₂) the-a₀₀ the-a₀₁
  the-a₀₂ = refl the-a₀₀

  the-a₁₀ : uncurry B (the-δ ₁₀)
  the-a₁₀ = f₁ ∙ a₁ 

  the-a₁₁ : uncurry B (the-δ ₁₁)
  the-a₁₁ = f₁ ∙ tr→ (Λ⇨ A) δ a₀

  the-a₁₂ : Id (Λ⇨ (uncurry B)) (the-δ ₁₂) the-a₁₀ the-a₁₁
  the-a₁₂ = coe→ (Id-AP {ε▸ (A (δ ₁))} (λ x → δ ₁ ∷ top x)
                        ([] ∷ a₁ ∷ tr→ (Λ⇨ A) δ a₀ ∷
                        utr→ (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀))
                        (Λ⇨ (uncurry {A = Λ⇨ A} B)) (f₁ ∙ a₁) (f₁ ∙ tr→ (Λ⇨ A) δ a₀))
                 (refl f₁ ∙ a₁ ∙ (tr→ (Λ⇨ A) δ a₀) ∙
                   (utr→ (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀)))

  the-a₂₁ : Id (Λ⇨ (uncurry B)) (the-δ ₂₁) the-a₀₁ the-a₁₁
  the-a₂₁ = lift← (Λ⇨ (uncurry {A = Λ⇨ A} B))
                  (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
                  (f₁ ∙ tr→ (Λ⇨ A) δ a₀)
            
  the-lift← : Id (Λ⇨ (uncurry B)) (δ ∷ a₀ ∷ a₁ ∷ a₂)
                 (tr← (Λ⇨ (uncurry B))
                      (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
                      (f₁ ∙ tr→ (Λ⇨ A) δ a₀))
                 (f₁ ∙ a₁)
  the-lift← = comp← {Δ = the-Δ} the-A the-δ
    {the-a₀₀} {the-a₀₁} the-a₀₂ {the-a₁₀} {the-a₁₁} the-a₁₂ the-a₂₁

postulate
  lift←Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₁ : Π (A (δ ₁)) (B (δ ₁))) →
    lift← (Λ w ⇨ Π (A w) (B w)) δ f₁ ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ Lift←Π.the-lift← A B δ f₁ a₀ a₁ a₂

{-# REWRITE lift←Π #-}
