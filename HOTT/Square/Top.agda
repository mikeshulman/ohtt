{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Square.Top where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base

----------------------------------------------------------------------
-- Extracting the components of a square in an extended telescope
----------------------------------------------------------------------

-- We put this in a separate file from Square because it's slow to
-- load and, I hope, rarely needed.  Taken together, these functions
-- are the inverse of sq∷.

popsq : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → el (SQ Δ)
popsq δ = pop (pop (pop (pop (pop (pop (pop (pop (pop δ))))))))

top₀₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₀₀)
top₀₀ δ = top (pop (pop (pop (pop (pop (pop (pop (pop δ))))))))

top₀₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₀₁)
top₀₁ δ = top (pop (pop (pop (pop (pop (pop (pop δ)))))))

top₀₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id′ A (popsq δ ₀₂) (top₀₀ δ) (top₀₁ δ)
top₀₂ δ = unfrob₀₂ _ (popsq δ) (top (pop (pop (pop (pop (pop (pop δ)))))))

top₁₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₁₀)
top₁₀ δ = top (pop (pop (pop (pop (pop δ)))))

top₁₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) → A (popsq δ ₁₁)
top₁₁ δ = top (pop (pop (pop (pop δ))))

top₁₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id′ A (popsq δ ₁₂) (top₁₀ δ) (top₁₁ δ)
top₁₂ δ = unfrob₁₂ _ (popsq δ) (top (pop (pop (pop (pop (pop (pop δ))))))) (top (pop (pop (pop δ))))

top₂₀ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id′ A (popsq δ ₂₀) (top₀₀ δ) (top₁₀ δ)
top₂₀ δ = top (pop (pop δ))

top₂₁ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Id′ A (popsq δ ₂₁) (top₀₁ δ) (top₁₁ δ)
top₂₁ δ = top (pop δ)

-- This looks messy, but it's just a bunch of heterogeneous equality
-- wrangling to apply the two frob-unfrob's in the right places.  It
-- would all disappear if frob-unfrob were rewrites, and should also
-- disappear on concrete types.
top₂₂ : {Δ : Tel} {A : el Δ → Type} (δ : el (SQ (Δ ▸ A))) →
  Sq A (popsq δ) {top₀₀ δ} {top₀₁ δ} (top₀₂ δ) {top₁₀ δ} {top₁₁ δ} (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
top₂₂ {Δ} {A} δ =
  coe← (Id′≡ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
             {popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ frob₀₂ A (popsq δ) (top₀₂ δ) ∷ top₁₀ δ ∷ top₁₁ δ ∷ frob₁₂ A (popsq δ) (top₀₂ δ) (top₁₂ δ)}
             {pop (pop (pop δ))}
             (∷≡ (λ x → Id′ (λ y → A ((pop y) ₁)) (pop (pop x)) (top (pop x)) (top x))
                  {popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ frob₀₂ A (popsq δ) (top₀₂ δ) ∷ top₁₀ δ ∷ top₁₁ δ}
                  {pop (pop (pop (pop δ)))}
                  (∷≡ (λ x → A ((pop (pop (pop (pop x)))) ₁₁))
                    {popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ frob₀₂ A (popsq δ) (top₀₂ δ) ∷ top₁₀ δ}
                    {pop (pop (pop (pop (pop δ))))}
                    (∷≡ (λ x → A ((pop (pop (pop x))) ₁₀))
                      {popsq δ ∷ top₀₀ δ ∷ top₀₁ δ ∷ frob₀₂ A (popsq δ) (top₀₂ δ)}
                      {pop (pop (pop (pop (pop (pop δ)))))}
                      (∷≡ (λ x → Id′ (λ y → A (y ₀)) (pop (pop x)) (top (pop x)) (top x))
                        {popsq δ ∷ top₀₀ δ ∷ top₀₁ δ} {pop (pop (pop (pop (pop (pop (pop δ))))))} reflᵉ
                        {frob₀₂ A (popsq δ) (top₀₂ δ)} {top (pop (pop (pop (pop (pop (pop δ))))))}
                        (≡→≡ʰ (frob-unfrob₀₂ A (popsq δ) (top (pop (pop (pop (pop (pop (pop δ))))))))))
                    {top₁₀ δ} {top₁₀ δ} reflʰ)
                  {top₁₁ δ} {top₁₁ δ} reflʰ)
                  {frob₁₂ A (popsq δ) (top₀₂ δ) (top₁₂ δ)} {top (pop (pop (pop δ)))}
                  (frob-unfrob₁₂ A (popsq δ) (top (pop (pop (pop (pop (pop (pop δ))))))) (top₀₂ δ) (top (pop (pop (pop δ))))))
             {top₂₀ δ} {top₂₀ δ} reflʰ {top₂₁ δ} {top₂₁ δ} reflʰ)
       (top δ)

-- If we were gluttons for punishment, we could try to prove that
-- these functions are the inverse of sq∷.
