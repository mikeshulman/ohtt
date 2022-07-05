{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Pi.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

--------------------
-- Π-types
--------------------

data Π (A : Type) (B : A → Type) : Type where
  ƛ⇒ : (f : (x : A) → B x) → Π A B

infixr 27 ƛ⇒
syntax ƛ⇒ (λ x → f) = ƛ x ⇒ f

syntax Π A (λ x → B) = Π[ x ﹕ A ] B

_∙_ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → B a
ƛ⇒ f ∙ a = f a

infixl 50 _∙_

infixr 30 _⇒_
_⇒_ : Type → Type → Type
A ⇒ B = Π[ x ﹕ A ] B

postulate
  ηΠ : {A : Type} {B : A → Type} (f : Π A B) → (ƛ x ⇒ f ∙ x) ≡ f

{-# REWRITE ηΠ #-}

postulate
  IdΠ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (λ a → B (δ ₀) a)) (f₁ : Π (A (δ ₁)) (λ a → B (δ ₁) a)) →
    Id (Λ w ⇨ Π (A w) (B w)) δ f₀ f₁ ≡
      Π[ a₀ ﹕ A (δ ₀) ] Π[ a₁ ﹕ A (δ ₁) ] Π[ a₂ ﹕ Id (Λ⇨ A) δ a₀ a₁ ]
        Id {Δ ▸ Λ⇨ A} (Λ⇨ (uncurry B)) (δ ∷ a₀ ∷ a₁ ∷ a₂) (f₀ ∙ a₀) (f₁ ∙ a₁)
  ＝Π : (A : Type) (B : A → Type) (f₀ f₁ : Π A B) →
    (f₀ ＝ f₁) ≡ Π[ a₀ ﹕ A ] Π[ a₁ ﹕ A ] Π[ a₂ ﹕ a₀ ＝ a₁ ]
      Id {ε▸ A} (Λ a ⇨ B (top a)) ([] ∷ a₀ ∷ a₁ ∷ a₂) (f₀ ∙ a₀) (f₁ ∙ a₁)

{-# REWRITE IdΠ ＝Π #-}

postulate
  apƛ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (f : (x : el Δ) (a : A x) → B x a) →
    ap (Λ x ⇨ Π (A x) (B x)) (λ x → ƛ y ⇒ f x y) δ ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ ap {Δ ▸ Λ⇨ A} (Λ⇨ (uncurry B)) (λ w → f (pop w) (top w)) (δ ∷ a₀ ∷ a₁ ∷ a₂) 
  reflƛ : (A : Type) (B : A → Type) (f : (a : A) → B a) →
    refl (ƛ x ⇒ f x) ≡
    ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ ap {ε▸ A} (Λ x ⇨ B (top x)) (λ x → f (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂)
  ap∙ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (f : (x : el Δ) → Π (A x) (B x)) (a : (x : el Δ) → A x) →
    ap (Λ x ⇨ B x (a x)) (λ x → f x ∙ a x) δ ≡
    coe← (Id-AP {Δ} {Δ ▸ Λ⇨ A} (λ x → x ∷ a x) δ (Λ⇨ (uncurry B))
                (f (δ ₀) ∙ a (δ ₀)) (f (δ ₁) ∙ a (δ ₁)))
         (ap (Λ x ⇨ Π (A x) (B x)) f δ ∙ (a (δ ₀)) ∙ (a (δ ₁)) ∙ (ap (Λ⇨ A) a δ))
  refl∙ : (A : Type) (B : A → Type) (f : Π A B) (a : A) →
    refl (f ∙ a) ≡
    coe← (Id-AP {ε} {ε▸ A} (λ _ → [] ∷ a) [] (Λ x ⇨ B (top x)) (f ∙ a) (f ∙ a))
          (refl f ∙ a ∙ a ∙ (refl a))

{-# REWRITE apƛ reflƛ ap∙ refl∙ #-}
