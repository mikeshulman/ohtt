{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Pi where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id

--------------------
-- Π-types
--------------------

postulate
  Π : (A : Type) (B : A → Type) → Type
  Λ : {A : Type} {B : A → Type} (f : (x : A) → B x) → Π A B
  _∙_ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → B a

infixl 30 _∙_

postulate
  β∙ : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) → (Λ f ∙ a) ≡ f a
  ηΛ : {A : Type} {B : A → Type} (f : Π A B) → Λ (λ x → f ∙ x) ≡ f

{-# REWRITE β∙ ηΛ #-}

postulate
  IdΠ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : Π (A δ₀) (λ a → B δ₀ a)) (f₁ : Π (A δ₁) (λ a → B δ₁ a)) →
    Id′ (λ w → Π (A w) (λ a → B w a)) δ₂ f₀ f₁ ≡
      Π (A δ₀) (λ a₀ →
      Π (A δ₁) (λ a₁ →
      Π (Id′ A δ₂ a₀ a₁) (λ a₂ →
        Id′ {Δ ▸ A} (uncurry B) {δ₀ ∷ a₀} {δ₁ ∷ a₁} (δ₂ ∷ a₂) (f₀ ∙ a₀) (f₁ ∙ a₁))))

{-# REWRITE IdΠ #-}

postulate
  apΛ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (f : (x : el Δ) (a : A x) → B x a) →
    ap (λ x → Λ (f x)) δ₂ ≡ Λ λ a₀ → Λ λ a₁ → Λ λ a₂ → ap (λ w → f (pop w) (top w)) {δ₀ ∷ a₀} {δ₁ ∷ a₁} (δ₂ ∷ a₂) 
  ap∙ :  {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (f : (x : el Δ) → Π (A x) (B x)) (a : (x : el Δ) → A x) →
    ap (λ x → f x ∙ a x) δ₂ ≡
    coe→ (Id-AP (λ w → (w ∷ a w)) {δ₀} {δ₁} δ₂ (uncurry B) _ _) (ap f δ₂ ∙ (a δ₀) ∙ (a δ₁) ∙ (ap a δ₂))

{-# REWRITE apΛ ap∙ #-}

-- Id-popΠ will have the same problem as Id-popΣ.

------------------------------
-- Function types
------------------------------

_⟶_ : Type → Type → Type
A ⟶ B = Π A (λ _ → B)

infixr 20 _⟶_

----------------------------------------
-- Transport in Π-types
----------------------------------------

postulate
  tr→Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : Π (A δ₀) (B δ₀)) →
    tr→ (λ w → Π (A w) (B w)) δ₂ f₀ ≡
    Λ λ a₁ → tr→ (uncurry B) {δ₀ ∷ tr← A δ₂ a₁} {δ₁ ∷ a₁} (δ₂ ∷ lift← A δ₂ a₁) (f₀ ∙ (tr← A δ₂ a₁))
  tr←Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₁ : Π (A δ₁) (B δ₁)) →
    tr← (λ w → Π (A w) (B w)) δ₂ f₁ ≡
    Λ λ a₀ → tr← (uncurry B) {δ₀ ∷ a₀} {δ₁ ∷ tr→ A δ₂ a₀} (δ₂ ∷ lift→ A δ₂ a₀) (f₁ ∙ (tr→ A δ₂ a₀))

{-# REWRITE tr→Π tr←Π #-}
{-
postulate
  foo : {A : Type} → Type → A

postulate
  lift→Π : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : Π (A δ₀) (B δ₀)) →
    lift→ (λ w → Π (A w) (B w)) δ₂ f₀ ≡
    Λ λ a₀ → Λ λ a₁ → Λ λ a₂ →
    {!!}

    -- Needs some 2D horn-filling...
{-
    foo (Id′ (uncurry B) {δ₀ ∷ a₀} {δ₀ ∷ tr← A δ₂ a₁}
             (REFL δ₀ ∷ coe← (Id-REFL A δ₀ a₀ (tr← A δ₂ a₁)) (utr← A δ₂ a₁ a₀ (tr← A δ₂ a₁) a₂ (lift← A δ₂ a₁)))
             (f₀ ∙ a₀) (f₀ ∙ tr← A δ₂ a₁))
-}
     -- ap {ε ▸ (λ _ → A δ₀)} (λ w → f₀ ∙ (top w)) {[] ∷ a₀} {[] ∷ tr← A δ₂ a₁} ([] ∷ utr← A δ₂ a₁ a₀ (tr← A δ₂ a₁) a₂ (lift← A δ₂ a₁))
     --lift→ (uncurry B) (δ₂ ∷ lift← A δ₂ a₁) (f₀ ∙ tr← A δ₂ a₁)
-}
