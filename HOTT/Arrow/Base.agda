{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Arrow.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Pi.Base

--------------------
-- Function-types
--------------------

-- As with product types and Σ-types, we could derive non-dependent
-- function types as a special case of dependent Π-types.  But many
-- things are simpler in the non-dependent case, so it's worth having
-- them defined separately.

data _⇒_ (A B : Type) : Type where
  lam⇒ : (f : A → B) → (A ⇒ B)

infixr 30 _⇒_

infixr 27 lam⇒
syntax lam⇒ (λ x → f) = Λ x ⇒ f

_∙_ : {A B : Type} (f : A ⇒ B) → A → B
lam⇒ f ∙ a = f a

infixl 30 _∙_

postulate
  η⇒ : {A B : Type} (f : A ⇒ B) → (Λ x ⇒ f ∙ x) ≡ f

{-# REWRITE η⇒ #-}

-- Note, though, that the identity types of non-dependent function
-- types require *dependent* function-types!  So unlike Prod, which is
-- completely independent of Sigma, we have to import Pi into Arrow.
postulate
  Id⇒ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) (f₁ : (A (δ ₁)) ⇒ (B (δ ₁))) →
    Id (λ w → (A w) ⇒ (B w)) δ f₀ f₁ ≡
      Π (A (δ ₀)) (λ a₀ →
      Π (A (δ ₁)) (λ a₁ →
      (Id A δ a₀ a₁) ⇒
        Id B δ (f₀ ∙ a₀) (f₁ ∙ a₁)))
  ＝⇒ : (A B : Type) (f₀ f₁ : A ⇒ B) →
    (f₀ ＝ f₁) ≡
      Π A (λ a₀ →
      Π A (λ a₁ →
      (a₀ ＝ a₁) ⇒
        (f₀ ∙ a₀ ＝ f₁ ∙ a₁)))

{-# REWRITE Id⇒ ＝⇒ #-}

-- Note that apΛ⇒ requires a coercion compared to apΛ.
postulate
  apΛ⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x → B x) →
    ap (λ x → Λ y ⇒ f x y) δ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒
    Id-pop← B A δ a₂ (ap {Δ ▸ A} (λ w → f (pop w) (top w)) (δ ∷ a₀ ∷ a₁ ∷ a₂))
  reflΛ⇒ : (A B : Type) (f : A → B) →
    refl (Λ x ⇒ f x) ≡ Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒ ap {ε ▸ (λ _ → A)} (λ x → f (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂)
  ap∙ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f : (x : el Δ) → (A x) ⇒ (B x)) (a : (x : el Δ) → A x) →
    ap (λ x → f x ∙ a x) δ ≡ (ap f δ ⊙ (a (δ ₀)) ⊙ (a (δ ₁)) ∙ (ap a δ))
  refl∙ : (A B : Type) (f : A ⇒ B) (a : A) →
    refl (f ∙ a) ≡ (refl f ⊙ a ⊙ a ∙ (refl a))

{-# REWRITE apΛ⇒ reflΛ⇒ ap∙ refl∙ #-}
