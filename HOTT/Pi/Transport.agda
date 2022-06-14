{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Pi.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Pi.Base

----------------------------------------
-- Transport in Π-types
----------------------------------------

postulate
  tr→Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (B (δ ₀))) →
    tr→ (λ w → Π (A w) (B w)) δ f₀ ≡
    Λ a₁ ⇛ tr→ (uncurry B) (δ ∷ tr← A δ a₁ ∷ a₁ ∷ lift← A δ a₁) (f₀ ⊙ (tr← A δ a₁))
  tr←Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₁ : Π (A (δ ₁)) (B (δ ₁))) →
    tr← (λ w → Π (A w) (B w)) δ f₁ ≡
    Λ a₀ ⇛ tr← (uncurry B) (δ ∷ a₀ ∷ tr→ A δ a₀ ∷ lift→ A δ a₀) (f₁ ⊙ (tr→ A δ a₀))

{-# REWRITE tr→Π tr←Π #-}

{-
postulate
  lift→Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (B (δ ₀))) →
    lift→ (λ w → Π (A w) (B w)) δ f₀ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇛
    comp← (uncurry B)
      {(δ ₀) ∷ a₀} {(δ ₀) ∷ tr← A δ a₁}
      (REFL (δ ₀) ∷ coe← (Id-REFL A (δ ₀) a₀ (tr← A δ a₁)) (utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁)))
      {(δ ₁) ∷ a₁} {(δ ₁) ∷ a₁}
      (REFL (δ ₁) ∷ coe← (Id-REFL A (δ ₁) a₁ a₁) (refl a₁))
      (δ ∷ a₂) (δ ∷ lift← A δ a₁)
      -- We need a square in (Δ ▸ A), and we need a way to make that
      -- from a square in Δ and a dependent square in A.  This
      -- requires some context rearranging, since a square in (Δ ▸ A)
      -- mixes the As in with the Δs in the contexts.
      {!(sq▸ A (REFL (δ ₀)) (REFL (δ ₁)) δ δ (DEGSQ-LR Δ δ)
           (coe← (Id-REFL A (δ ₀) a₀ (tr← A δ a₁)) (utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁)))
           (coe← (Id-REFL A (δ ₁) a₁ a₁) (refl a₁))
           a₂ (lift← A δ a₁)
           ((coe→ (cong (λ ρ → Id′ {TID Δ ▸ (λ w → A (left {Δ} w)) ▸ (λ w → A (right {Δ} (pop {TID Δ} {λ w₁ → A (left {Δ} w₁)} w)))}
                                   (λ w → Id′ A (mid {Δ} (pop (pop w))) (top (pop w)) (top w))
                                   {tot (δ ₀) (δ ₁) δ ∷ a₀ ∷ a₁} {tot (δ ₀) (δ ₁) δ ∷ (tr← A δ a₁) ∷ a₁} ρ
                                   a₂ (lift← A δ a₁))
           -- Now we need to prove that tsq-tb-lift, in the special
           -- case of our partially degenerate square, specializes to
           -- something that arose otherwise.
                        {! !})
             (coe← (Id-AP {ε ▸ (λ _ → A (δ ₀))} {TID Δ ▸ (λ w → A (left w)) ▸ (λ w → A (right (pop w)))}
                  (λ z → tot (δ ₀) (δ ₁) δ ∷ top z ∷ a₁)
                  {[] ∷ a₀} {[] ∷ tr← A δ a₁}
                  ([] ∷ utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁))
                  (λ w → Id′ {Δ} A (mid {Δ} (pop (pop w))) (top (pop w)) (top w))
                  a₂ (lift← A δ a₁))
              (ulift← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁))))))!}
      {f₀ ⊙ a₀} {f₀ ⊙ tr← A δ a₁}
      (coe← {!(Id-REFL∷ A (uncurry B) (δ ₀) (utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁)) (f₀ ⊙ a₀) (f₀ ⊙ tr← A δ a₁))!}
        (ap {ε ▸ (λ _ → A (δ ₀))} (λ w → f₀ ⊙ (top w))
            {[] ∷ a₀} {[] ∷ tr← A δ a₁} ([] ∷ utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁))))
      {tr→ (uncurry B) {(δ ₀) ∷ tr← A δ a₁} {(δ ₁) ∷ a₁} (δ ∷ lift← A δ a₁) (f₀ ⊙ (tr← A δ a₁))}
      {tr→ (uncurry B) {(δ ₀) ∷ tr← A δ a₁} {(δ ₁) ∷ a₁} (δ ∷ lift← A δ a₁) (f₀ ⊙ (tr← A δ a₁))}
      (coe← (Id-REFL (uncurry B) ((δ ₁) ∷ a₁) (tr→ (uncurry B) {(δ ₀) ∷ tr← A δ a₁} {(δ ₁) ∷ a₁} (δ ∷ lift← A δ a₁) (f₀ ⊙ tr← A δ a₁))
                                           (tr→ (uncurry B) {(δ ₀) ∷ tr← A δ a₁} {(δ ₁) ∷ a₁} (δ ∷ lift← A δ a₁) (f₀ ⊙ tr← A δ a₁)))
        (refl (tr→ (uncurry B) {(δ ₀) ∷ tr← A δ a₁} {(δ ₁) ∷ a₁} (δ ∷ lift← A δ a₁) (f₀ ⊙ (tr← A δ a₁)))))
      (lift→ (uncurry B) {(δ ₀) ∷ tr← A δ a₁} {(δ ₁) ∷ a₁} (δ ∷ lift← A δ a₁) (f₀ ⊙ tr← A δ a₁)) 
-}
