{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

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
  tr→⇛ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₀ : (A (δ ₀)) ⇛ (B (δ ₀))) →
    tr→ (Λ w ⇨ (A w) ⇛ (B w)) δ f₀ ≡ ƛ a₁ ⇛ tr→ (Λ⇨ B) δ (f₀ ⊙ (tr← (Λ⇨ A) δ a₁))
  tr←⇛ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₁ : (A (δ ₁)) ⇛ (B (δ ₁))) →
    tr← (Λ w ⇨ (A w) ⇛ (B w)) δ f₁ ≡ ƛ a₀ ⇛ tr← (Λ⇨ B) δ (f₁ ⊙ (tr→ (Λ⇨ A) δ a₀))

{-# REWRITE tr→⇛ tr←⇛ #-}

postulate
  lift→⇛ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₀ : (A (δ ₀)) ⇛ (B (δ ₀))) →
    lift→ (Λ w ⇨ (A w) ⇛ (B w)) δ f₀ ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇛
      comp↓ (Λ⇨ B) (DEGSQ-TB δ)
            (lift→ (Λ⇨ B) δ (f₀ ⊙ tr← (Λ⇨ A) δ a₁))
            (refl f₀ ∙ a₀ ∙ tr← (Λ⇨ A) δ a₁ ⊙ (utr← (Λ⇨ A) δ a₁ a₀ (tr← (Λ⇨ A) δ a₁) a₂ (lift← (Λ⇨ A) δ a₁)))
            (refl (tr→ (Λ⇨ B) δ (f₀ ⊙ tr← (Λ⇨ A) δ a₁)))
  lift←⇛ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₁ : (A (δ ₁)) ⇛ (B (δ ₁))) →
    lift← (Λ w ⇨ (A w) ⇛ (B w)) δ f₁ ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇛
      comp↓ (Λ⇨ B) (DEGSQ-TB δ)
            (lift← (Λ⇨ B) δ (f₁ ⊙ tr→ (Λ⇨ A) δ a₀))
            (refl (tr← (Λ⇨ B) δ (f₁ ⊙ tr→ (Λ⇨ A) δ a₀)))
            (refl f₁ ∙ a₁ ∙ tr→ (Λ⇨ A) δ a₀ ⊙ (utr→ (Λ⇨ A) δ a₀ a₁ (tr→ (Λ⇨ A) δ a₀) a₂ (lift→ (Λ⇨ A) δ a₀)))

{-# REWRITE lift→⇛ lift←⇛ #-}

-- Again, we deduce utr and ulift from square-filling.  It might
-- conceivably be feasible to do these explicitly, but it's not worth
-- the trouble.

postulate
  utr→⇛ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : (A (δ ₀)) ⇛ (B (δ ₀))) (u₁ u₁' : (A (δ ₁)) ⇛ (B (δ ₁)))
    (u₂ : Id (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁) (u₂' : Id (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁') →
    utr→      (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-utr→ (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁ u₁' u₂ u₂'
  utr←⇛ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : (A (δ ₁)) ⇛ (B (δ ₁))) (u₀ u₀' : (A (δ ₀)) ⇛ (B (δ ₀)))
    (u₂ : Id (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁) (u₂' : Id (Λ w ⇨ (A w) ⇛ (B w)) δ u₀' u₁) →
    utr←      (Λ w ⇨ (A w) ⇛ (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-utr← (Λ w ⇨ (A w) ⇛ (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE utr→⇛ utr←⇛ #-}

postulate
  ulift→⇛ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₀ : (A (δ ₀)) ⇛ (B (δ ₀))) (u₁ u₁' : (A (δ ₁)) ⇛ (B (δ ₁)))
    (u₂ : Id (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁) (u₂' : Id (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁') →
    ulift→      (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁ u₁' u₂ u₂' ≡
    fill-ulift→ (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁ u₁' u₂ u₂'
  ulift←⇛ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (u₁ : (A (δ ₁)) ⇛ (B (δ ₁))) (u₀ u₀' : (A (δ ₀)) ⇛ (B (δ ₀)))
    (u₂ : Id (Λ w ⇨ (A w) ⇛ (B w)) δ u₀ u₁) (u₂' : Id (Λ w ⇨ (A w) ⇛ (B w)) δ u₀' u₁) →
    ulift←      (Λ w ⇨ (A w) ⇛ (B w)) δ u₁ u₀ u₀' u₂ u₂' ≡
    fill-ulift← (Λ w ⇨ (A w) ⇛ (B w)) δ u₁ u₀ u₀' u₂ u₂'

{-# REWRITE ulift→⇛ ulift←⇛ #-}
