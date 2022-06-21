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

postulate
  utr→⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) (f₁ f₁' : (A (δ ₁)) ⇒ (B (δ ₁))) (f₂ : Id′ (λ w → A w ⇒ B w) δ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ f₀ f₁') →
    utr→ (λ w → (A w) ⇒ (B w)) δ f₀ f₁ f₁' f₂ f₂' ≡
    Λ a₁ ⇛ Λ a₁' ⇛ Λ a₂ ⇒
     comp→ B (DEGSQ-TB δ)
            (f₂ ⊙ (tr← A δ a₁) ⊙ a₁ ∙ (lift← A δ a₁))
            (f₂' ⊙ (tr← A δ a₁') ⊙ a₁' ∙ (lift← A δ a₁'))
            (ap {ε ▸ (λ _ → A (δ ₁))} (λ x → f₀ ∙ tr← A δ (top x)) ([] ∷ a₁ ∷ a₁' ∷ a₂))
  utr←⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f₁ : (A (δ ₁)) ⇒ (B (δ ₁))) (f₀ f₀' : (A (δ ₀)) ⇒ (B (δ ₀))) (f₂ : Id′ (λ w → A w ⇒ B w) δ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ f₀' f₁) →
    utr← (λ w → (A w) ⇒ (B w)) δ f₁ f₀ f₀' f₂ f₂' ≡
    Λ a₀ ⇛ Λ a₀' ⇛ Λ a₂ ⇒
     comp← B (DEGSQ-TB δ)
            (f₂ ⊙ a₀ ⊙ (tr→ A δ a₀) ∙ (lift→ A δ a₀))
            (f₂' ⊙ a₀' ⊙ (tr→ A δ a₀') ∙ (lift→ A δ a₀'))
            (ap {ε ▸ (λ _ → A (δ ₀))} (λ x → f₁ ∙ tr→ A δ (top x)) ([] ∷ a₀ ∷ a₀' ∷ a₂))

{-# REWRITE utr→⇒ utr←⇒ #-}

{-
postulate
  ulift→⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) (f₁ f₁' : (A (δ ₁)) ⇒ (B (δ ₁))) (f₂ : Id′ (λ w → A w ⇒ B w) δ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ f₀ f₁') →
    ulift→ (λ w → (A w) ⇒ (B w)) δ f₀ f₁ f₁' f₂ f₂' ≡
    Λ a₀₀ ⇛ Λ a₁₀ ⇛ Λ a₂₀ ⇛ Λ a₀₁ ⇛ Λ a₁₁ ⇛ Λ a₂₁ ⇛ Λ a₀₂ ⇛ Λ a₁₂ ⇛ Λ a₂₂ ⇒
      {!!} -- This looks like it might start to get into 3-cube territory.
-}
