{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Pi.Transport.Lift where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Pi.Transport.Tr

postulate
  lift→Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (B (δ ₀))) →
    lift→ (λ w → Π (A w) (B w)) δ f₀ ≡
    Λ a₀ ⇒ Λ a₁ ⇒ Λ a₂ ⇒
    (comp← {Δ ▸ A} (uncurry B)
      (sq∷ A (DEGSQ-LR δ)
           {a₀} {tr← A δ a₁}
           (utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁))
           {a₁} {a₁}
           (Id-pop→ (λ x → A (x ₁)) (λ x → A (x ₀)) (DEGSQ-LR δ)
             (utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁)) (refl a₁))
           a₂
           (lift← A δ a₁)
           (ulift←sq A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁)))
      {f₀ ∙ a₀} {f₀ ∙ tr← A δ a₁}
      (coe← (Id-AP (λ x → δ ₀ ∷ top x)
                    ([] ∷ a₀ ∷ tr← A δ a₁ ∷ utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁))
                    (uncurry B) (f₀ ∙ a₀) (f₀ ∙ tr← A δ a₁))
            (refl f₀ ∙ a₀ ∙ (tr← A δ a₁) ∙ (utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁))))
      {tr→ (uncurry B) (δ ∷ tr← A δ a₁ ∷ a₁ ∷ lift← A δ a₁) (f₀ ∙ tr← A δ a₁)}
      {tr→ (uncurry B) (δ ∷ tr← A δ a₁ ∷ a₁ ∷ lift← A δ a₁) (f₀ ∙ tr← A δ a₁)}
      (refl (tr→ (uncurry B) (δ ∷ tr← A δ a₁ ∷ a₁ ∷ lift← A δ a₁) (f₀ ∙ tr← A δ a₁)))
      (lift→ (uncurry B) (δ ∷ tr← A δ a₁ ∷ a₁ ∷ lift← A δ a₁) (f₀ ∙ tr← A δ a₁)))
  lift←Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₁ : Π (A (δ ₁)) (B (δ ₁))) →
    lift← (λ w → Π (A w) (B w)) δ f₁ ≡
    Λ a₀ ⇒ Λ a₁ ⇒ Λ a₂ ⇒
    (comp← {Δ ▸ A} (uncurry B)
      (sq∷ A (DEGSQ-LR δ)
           {a₀} {a₀} (refl a₀)
           {a₁} {tr→ A δ a₀}
           (utr→ A δ a₀ a₁ (tr→ A δ a₀) a₂ (lift→ A δ a₀))
           a₂
           (lift→ A δ a₀)
           (ulift→sq A δ a₀ a₁ (tr→ A δ a₀) a₂ (lift→ A δ a₀)))
      {tr← (uncurry B) (δ ∷ a₀ ∷ tr→ A δ a₀ ∷ lift→ A δ a₀) (f₁ ∙ tr→ A δ a₀)}
      {tr← (uncurry B) (δ ∷ a₀ ∷ tr→ A δ a₀ ∷ lift→ A δ a₀) (f₁ ∙ tr→ A δ a₀)}
      (refl (tr← (uncurry B) (δ ∷ a₀ ∷ tr→ A δ a₀ ∷ lift→ A δ a₀) (f₁ ∙ tr→ A δ a₀)))
      {f₁ ∙ a₁} {f₁ ∙ tr→ A δ a₀}
      (coe← (Id-AP (λ x → δ ₁ ∷ top x)
                    ([] ∷ a₁ ∷ tr→ A δ a₀ ∷ utr→ A δ a₀ a₁ (tr→ A δ a₀) a₂ (lift→ A δ a₀))
                    (uncurry B) (f₁ ∙ a₁) (f₁ ∙ tr→ A δ a₀))
            (refl f₁ ∙ a₁ ∙ (tr→ A δ a₀) ∙ (utr→ A δ a₀ a₁ (tr→ A δ a₀) a₂ (lift→ A δ a₀))))
      (lift← (uncurry B) (δ ∷ a₀ ∷ tr→ A δ a₀ ∷ lift→ A δ a₀) (f₁ ∙ tr→ A δ a₀)))

{-# REWRITE lift→Π lift←Π #-}
