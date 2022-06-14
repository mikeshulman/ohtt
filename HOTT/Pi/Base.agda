{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Pi.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

--------------------
-- Π-types
--------------------

postulate
  Π : (A : Type) (B : A → Type) → Type
  lamΠ : {A : Type} {B : A → Type} (f : (x : A) → B x) → Π A B
  _⊙_ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → B a

infixr 27 lamΠ
syntax lamΠ (λ x → f) = Λ x ⇛ f

infixl 30 _⊙_

postulate
  β⊙ : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) → ((Λ x ⇛ f x) ⊙ a) ≡ f a
  ηΠ : {A : Type} {B : A → Type} (f : Π A B) → (Λ x ⇛ f ⊙ x) ≡ f

{-# REWRITE β⊙ ηΠ #-}

postulate
  Id′Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (f₀ : Π (A (δ ₀)) (λ a → B (δ ₀) a)) (f₁ : Π (A (δ ₁)) (λ a → B (δ ₁) a)) →
    Id′ (λ w → Π (A w) (λ a → B w a)) δ f₀ f₁ ≡
      Π (A (δ ₀)) (λ a₀ →
      Π (A (δ ₁)) (λ a₁ →
      Π (Id′ A δ a₀ a₁) (λ a₂ →
        Id′ {Δ ▸ A} (uncurry B) (δ ∷ a₀ ∷ a₁ ∷ a₂) (f₀ ⊙ a₀) (f₁ ⊙ a₁))))
  IdΠ : (A : Type) (B : A → Type) (f₀ f₁ : Π A B) →
    Id (Π A B) f₀ f₁ ≡
      Π A (λ a₀ →
      Π A (λ a₁ →
      Π (Id A a₀ a₁) (λ a₂ →
        Id′ {ε ▸ (λ _ → A)} (λ a → B (top a)) ([] ∷ a₀ ∷ a₁ ∷ a₂) (f₀ ⊙ a₀) (f₁ ⊙ a₁))))

{-# REWRITE Id′Π IdΠ #-}

postulate
  apΛ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (f : (x : el Δ) (a : A x) → B x a) →
    ap (λ x → Λ y ⇛ f x y) δ ≡ Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇛ ap (λ w → f (pop w) (top w)) (δ ∷ a₀ ∷ a₁ ∷ a₂) 
  reflΛ : (A : Type) (B : A → Type) (f : (a : A) → B a) →
    refl (Λ x ⇛ f x) ≡ Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇛ ap {ε ▸ (λ _ → A)} (λ x → f (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂)
  ap⊙ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) (δ : el (ID Δ))
    (f : (x : el Δ) → Π (A x) (B x)) (a : (x : el Δ) → A x) →
    ap (λ x → f x ⊙ a x) δ ≡
    coe← (Id′-AP (λ w → (w ∷ a w)) δ (uncurry B) _ _) (ap f δ ⊙ (a (δ ₀)) ⊙ (a (δ ₁)) ⊙ (ap a δ))
  refl⊙ : (A : Type) (B : A → Type) (f : Π A B) (a : A) →
    refl (f ⊙ a) ≡ coe← (Id′-AP {ε} (λ _ → [] ∷ a) [] (λ x → B (top x)) (f ⊙ a) (f ⊙ a)) (refl f ⊙ a ⊙ a ⊙ (refl a))

{-# REWRITE apΛ reflΛ ap⊙ refl⊙ #-}

-- TODO: Compute Id′-AP and ap-AP