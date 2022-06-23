{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Arrow.Transport where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Square.Degenerate
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Arrow.Base

----------------------------------------
-- Transport in function-types
----------------------------------------

-- tr→ and tr← are only slightly simpler in the non-dependent case.
postulate
  tr→⇒ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) →
    tr→ (λ w → (A w) ⇒ (B w)) δ f₀ ≡ Λ a₁ ⇒ tr→ B δ (f₀ ∙ (tr← A δ a₁))
  tr←⇒ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₁ : (A (δ ₁)) ⇒ (B (δ ₁))) →
    tr← (λ w → (A w) ⇒ (B w)) δ f₁ ≡ Λ a₀ ⇒ tr← B δ (f₁ ∙ (tr→ A δ a₀))

{-# REWRITE tr→⇒ tr←⇒ #-}

postulate
  lift→⇒ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) →
    lift→ (λ w → (A w) ⇒ (B w)) δ f₀ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒
      comp↓ B (DEGSQ-TB δ)
            (lift→ B δ (f₀ ∙ tr← A δ a₁))
            (refl f₀ ⊙ a₀ ⊙ tr← A δ a₁ ∙ (utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁)))
            (refl (tr→ B δ (f₀ ∙ tr← A δ a₁)))
  lift←⇒ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₁ : (A (δ ₁)) ⇒ (B (δ ₁))) →
    lift← (λ w → (A w) ⇒ (B w)) δ f₁ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒
      comp↓ B (DEGSQ-TB δ)
            (lift← B δ (f₁ ∙ tr→ A δ a₀))
            (refl (tr← B δ (f₁ ∙ tr→ A δ a₀)))
            (refl f₁ ⊙ a₁ ⊙ tr→ A δ a₀ ∙ (utr→ A δ a₀ a₁ (tr→ A δ a₀) a₂ (lift→ A δ a₀)))

{-# REWRITE lift→⇒ lift←⇒ #-}

-- Again, we deduce utr and ulift from square-filling.

postulate
  utr→⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : (A (δ ₀)) ⇒ (B (δ ₀))) (u₁ u₁' : (A (δ ₁)) ⇒ (B (δ ₁)))
    (u₂ : Id′ (λ w → (A w) ⇒ (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → (A w) ⇒ (B w)) δ u₀ u₁') →
    utr→      (λ w → (A w) ⇒ (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-utr→ (λ w → (A w) ⇒ (B w)) δ u₀ u₁ u₁' u₂ u₂'
  utr←⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : (A (δ ₁)) ⇒ (B (δ ₁))) (u₀ u₀' : (A (δ ₀)) ⇒ (B (δ ₀)))
    (u₂ : Id′ (λ w → (A w) ⇒ (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → (A w) ⇒ (B w)) δ u₀' u₁) →
    utr←      (λ w → (A w) ⇒ (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-utr← (λ w → (A w) ⇒ (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE utr→⇒ utr←⇒ #-}

postulate
  ulift→⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : (A (δ ₀)) ⇒ (B (δ ₀))) (u₁ u₁' : (A (δ ₁)) ⇒ (B (δ ₁)))
    (u₂ : Id′ (λ w → (A w) ⇒ (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → (A w) ⇒ (B w)) δ u₀ u₁') →
    ulift→      (λ w → (A w) ⇒ (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-ulift→ (λ w → (A w) ⇒ (B w)) δ u₀ u₁ u₁' u₂ u₂'
  ulift←⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : (A (δ ₁)) ⇒ (B (δ ₁))) (u₀ u₀' : (A (δ ₀)) ⇒ (B (δ ₀)))
    (u₂ : Id′ (λ w → (A w) ⇒ (B w)) δ u₀ u₁) (u₂' : Id′ (λ w → (A w) ⇒ (B w)) δ u₀' u₁) →
    ulift←      (λ w → (A w) ⇒ (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-ulift← (λ w → (A w) ⇒ (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE ulift→⇒ ulift←⇒ #-}
