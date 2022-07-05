{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Arrow.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Pi.Base

infixl 40 _⊙_
infixr 30 _⇛_
infixr 20 ƛ⇛

--------------------
-- Function-types
--------------------

-- As with product types and Σ-types, we could derive non-dependent
-- function types as a special case of dependent Π-types.  But many
-- things are simpler in the non-dependent case, so it's worth having
-- them defined separately.

data _⇛_ (A B : Type) : Type where
  ƛ⇛ : (f : A → B) → (A ⇛ B)

syntax ƛ⇛ (λ x → f) = ƛ x ⇛ f

_⊙_ : {A B : Type} (f : A ⇛ B) → A → B
ƛ⇛ f ⊙ a = f a

postulate
  η⇛ : {A B : Type} (f : A ⇛ B) → (ƛ x ⇛ f ⊙ x) ≡ f

{-# REWRITE η⇛ #-}

-- Note, though, that the identity types of non-dependent function
-- types require *dependent* function-types!  So unlike Prod, which is
-- completely independent of Sigma, we have to import Pi into Arrow.
postulate
  Id⇛ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₀ : (A (δ ₀)) ⇛ (B (δ ₀))) (f₁ : (A (δ ₁)) ⇛ (B (δ ₁))) →
    Id (Λ w ⇨ (A w) ⇛ (B w)) δ f₀ f₁ ≡
      Π[ a₀ ﹕ A (δ ₀) ] Π[ a₁ ﹕ A (δ ₁) ]
      (Id (Λ⇨ A) δ a₀ a₁) ⇛ Id (Λ⇨ B) δ (f₀ ⊙ a₀) (f₁ ⊙ a₁)
  ＝⇛ : (A B : Type) (f₀ f₁ : A ⇛ B) →
    (f₀ ＝ f₁) ≡ Π[ a₀ ﹕ A ] Π[ a₁ ﹕ A ] (a₀ ＝ a₁) ⇛ (f₀ ⊙ a₀ ＝ f₁ ⊙ a₁)

{-# REWRITE Id⇛ ＝⇛ #-}

postulate
  apƛ⇛ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x → B x) →
    ap (Λ x ⇨ A x ⇛ B x) (λ x → ƛ y ⇛ f x y) δ ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇛
    ap {Δ ▸ Λ⇨ A} (Λ⇨ B ⊚ POP) (λ w → f (pop w) (top w)) (δ ∷ a₀ ∷ a₁ ∷ a₂)
  reflƛ⇛ : (A B : Type) (f : A → B) →
    refl (ƛ x ⇛ f x) ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇛
    ap {ε▸ A} ((Λ _ ⇨ B) ⊚ POP) (λ x → f (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂)
  ap⊙ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f : (x : el Δ) → (A x) ⇛ (B x)) (a : (x : el Δ) → A x) →
    ap (Λ⇨ B) (λ x → f x ⊙ a x) δ ≡
    ap (Λ x ⇨ A x ⇛ B x) f δ ∙ (a (δ ₀)) ∙ (a (δ ₁)) ⊙ (ap (Λ⇨ A) a δ)
  refl⊙ : (A B : Type) (f : A ⇛ B) (a : A) →
    refl (f ⊙ a) ≡ (refl f ∙ a ∙ a ⊙ (refl a))

{-# REWRITE apƛ⇛ reflƛ⇛ ap⊙ refl⊙ #-}
