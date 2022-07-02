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
    lift→ (Λ w ⇨ Π (A w) (B w)) δ f₀ ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒
    (comp← {Δ ▸ Λ⇨ A} (Λ⇨ (uncurry {A = Λ⇨ A} B))
      (sq∷ (Λ⇨ A) (DEGSQ-LR δ)
           {a₀} {tr← (Λ⇨ A) δ a₁}
           (utr← (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁))
           {a₁} {a₁} (refl a₁) a₂ (lift← (Λ⇨ A) δ a₁)
           (ulift←sq (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁)))
      {f₀ ∙ a₀} {f₀ ∙ tr← (Λ⇨ A) δ a₁}
      (coe→ (Id-AP {ε▸ (A (δ ₀))} (λ x → δ ₀ ∷ top x)
                    ([] ∷ a₀ ∷ tr← (Λ⇨ A) δ a₁ ∷
                      utr← (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁))
                    (Λ⇨ (uncurry {A = Λ⇨ A} B))
                    (f₀ ∙ a₀) (f₀ ∙ tr← (Λ⇨ A) δ a₁))
            (refl f₀ ∙ a₀ ∙ (tr← (Λ⇨ A) δ a₁) ∙
              (utr← (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁))))
      {tr→ (Λ⇨ (uncurry {A = Λ⇨ A} B))
           (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁) (f₀ ∙ tr← (Λ⇨ A) δ a₁)}
      {tr→ (Λ⇨ (uncurry {A = Λ⇨ A} B))
           (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁) (f₀ ∙ tr← (Λ⇨ A) δ a₁)}
      -- Why does Id-REFL▸ not rewrite here?
      (coe→ (Id-AP {ε} {Δ ▸ Λ⇨ A} (λ _ → δ ₁ ∷ a₁) [] (Λ⇨ (uncurry {A = Λ⇨ A} B))
                   (tr→ (Λ⇨ (uncurry {A = Λ⇨ A} B))
                        (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁)
                        (f₀ ∙ tr← (Λ⇨ A) δ a₁))
                   (tr→ (Λ⇨ (uncurry {A = Λ⇨ A} B))
                        (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁)
                        (f₀ ∙ tr← (Λ⇨ A) δ a₁)))
            (refl (tr→ (Λ⇨ (uncurry {A = Λ⇨ A} B))
                       (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁)
                       (f₀ ∙ tr← (Λ⇨ A) δ a₁))))
      (lift→ (Λ⇨ (uncurry {A = Λ⇨ A} B))
             (δ ∷ tr← (Λ⇨ A) δ a₁ ∷ a₁ ∷ lift← (Λ⇨ A) δ a₁)
             (f₀ ∙ tr← (Λ⇨ A) δ a₁)))
  lift←Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₁ : Π (A (δ ₁)) (B (δ ₁))) →
    lift← (Λ w ⇨ Π (A w) (B w)) δ f₁ ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒
    (comp← {Δ ▸ Λ⇨ A} (Λ⇨ (uncurry {A = Λ⇨ A} B))
      (sq∷ (Λ⇨ A) (DEGSQ-LR δ)
           {a₀} {a₀} (refl a₀)
           {a₁} {tr→ (Λ⇨ A) δ a₀}
           (utr→ (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀))
           a₂ (lift→ (Λ⇨ A) δ a₀)
           (ulift→sq (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀)))
      {tr← (Λ⇨ (uncurry {A = Λ⇨ A} B))
           (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
           (f₁ ∙ tr→ (Λ⇨ A) δ a₀)}
      {tr← (Λ⇨ (uncurry {A = Λ⇨ A} B))
           (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
           (f₁ ∙ tr→ (Λ⇨ A) δ a₀)}
      (coe→ (Id-AP {ε} {Δ ▸ Λ⇨ A} (λ _ → δ ₀ ∷ a₀) [] (Λ⇨ (uncurry {A = Λ⇨ A} B))
                   (tr← (Λ⇨ (uncurry {A = Λ⇨ A} B))
                        (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
                        (f₁ ∙ tr→ (Λ⇨ A) δ a₀))
                   (tr← (Λ⇨ (uncurry {A = Λ⇨ A} B))
                        (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
                        (f₁ ∙ tr→ (Λ⇨ A) δ a₀)))
             (refl (tr← (Λ⇨ (uncurry {A = Λ⇨ A} B))
                   (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀)
                   (f₁ ∙ tr→ (Λ⇨ A) δ a₀))))
      {f₁ ∙ a₁} {f₁ ∙ tr→ (Λ⇨ A) δ a₀}
      (coe→ (Id-AP {ε▸ (A (δ ₁))} (λ x → δ ₁ ∷ top x)
                   ([] ∷ a₁ ∷ tr→ (Λ⇨ A) δ a₀ ∷
                     utr→ (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀))
                   (Λ⇨ (uncurry {A = Λ⇨ A} B)) (f₁ ∙ a₁) (f₁ ∙ tr→ (Λ⇨ A) δ a₀))
            (refl f₁ ∙ a₁ ∙ (tr→ (Λ⇨ A) δ a₀) ∙ (utr→ (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀))))
      (lift← (Λ⇨ (uncurry {A = Λ⇨ A} B)) (δ ∷ a₀ ∷ tr→ (Λ⇨ A) δ a₀ ∷ lift→ (Λ⇨ A) δ a₀) (f₁ ∙ tr→ (Λ⇨ A) δ a₀)))

{-# REWRITE lift→Π lift←Π #-}
