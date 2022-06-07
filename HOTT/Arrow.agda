{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Arrow where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Transport
open import HOTT.Square
open import HOTT.Fill
open import HOTT.Pi

--------------------
-- Function-types
--------------------

postulate
  _⇒_ : Type → Type → Type
  lam⇒ : {A B : Type} (f : A → B) → (A ⇒ B)
  _∙_ : {A B : Type} (f : A ⇒ B) → A → B

infixr 30 _⇒_

infixr 27 lam⇒
syntax lam⇒ (λ x → f) = Λ x ⇒ f

infixl 30 _∙_

postulate
  β∙ : {A B : Type} (f : A → B) (a : A) → ((Λ x ⇒ f x) ∙ a) ≡ f a
  η⇒ : {A B : Type} (f : A ⇒ B) → (Λ x ⇒ f ∙ x) ≡ f

{-# REWRITE β∙ η⇒ #-}

-- Note that the definition of the identity types of non-dependent
-- function types requires *dependent* function-types!  So unlike Prod
-- which is independent of Sigma, we have to import Pi into Arrow.
postulate
  Id′⇒ : {Δ : Tel} (A B : el Δ → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : (A δ₀) ⇒ (B δ₀)) (f₁ : (A δ₁) ⇒ (B δ₁)) →
    Id′ (λ w → (A w) ⇒ (B w)) δ₂ f₀ f₁ ≡
      Π (A δ₀) (λ a₀ →
      Π (A δ₁) (λ a₁ →
      (Id′ A δ₂ a₀ a₁) ⇒
        Id′ B δ₂ (f₀ ∙ a₀) (f₁ ∙ a₁)))
  Id⇒ : (A B : Type) (f₀ f₁ : A ⇒ B) →
    Id (A ⇒ B) f₀ f₁ ≡
      Π A (λ a₀ →
      Π A (λ a₁ →
      (Id A a₀ a₁) ⇒
        Id B (f₀ ∙ a₀) (f₁ ∙ a₁)))

{-# REWRITE Id′⇒ Id⇒ #-}

-- Also note that although ap∙ and refl∙ are simpler than ap⊙ and
-- refl⊙, lacking coercions, apΛ⇒ requires an additional coercion
-- compared to apΛ.
postulate
  apΛ⇒ : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f : (x : el Δ) → A x → B x) →
    ap (λ x → Λ y ⇒ f x y) δ₂ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒  coe← (Id′-AP {Δ ▸ A} pop {δ₀ ∷ a₀} {δ₁ ∷ a₁} (δ₂ ∷ a₂) B (f δ₀ a₀) (f δ₁ a₁))
                                 (ap (λ w → f (pop w) (top w)) {δ₀ ∷ a₀} {δ₁ ∷ a₁} (δ₂ ∷ a₂))  
  reflΛ⇒ : (A B : Type) (f : A → B) →
    refl (Λ x ⇒ f x) ≡ Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒ ap {ε ▸ (λ _ → A)} (λ x → f (top x)) {[] ∷ a₀} {[] ∷ a₁} ([] ∷ a₂)
  ap∙ : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (f : (x : el Δ) → (A x) ⇒ (B x)) (a : (x : el Δ) → A x) →
    ap (λ x → f x ∙ a x) δ₂ ≡ (ap f δ₂ ⊙ (a δ₀) ⊙ (a δ₁) ∙ (ap a δ₂))
  refl∙ : (A B : Type) (f : A ⇒ B) (a : A) →
    refl (f ∙ a) ≡ (refl f ⊙ a ⊙ a ∙ (refl a))

{-# REWRITE apΛ⇒ reflΛ⇒ ap∙ refl∙ #-}

----------------------------------------
-- Transport in function-types
----------------------------------------

postulate
  tr→⇒ : {Δ : Tel} (A B : el Δ → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : (A δ₀) ⇒ (B δ₀)) →
    tr→ (λ w → (A w) ⇒ (B w)) δ₂ f₀ ≡ Λ a₁ ⇒ tr→ B {δ₀} {δ₁} δ₂ (f₀ ∙ (tr← A δ₂ a₁))
  tr←⇒ : {Δ : Tel} (A B : el Δ → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₁ : (A δ₁) ⇒ (B δ₁)) →
    tr← (λ w → (A w) ⇒ (B w)) δ₂ f₁ ≡ Λ a₀ ⇒ tr← B {δ₀} {δ₁} δ₂ (f₁ ∙ (tr→ A δ₂ a₀))

{-# REWRITE tr→⇒ tr←⇒ #-}

{-
postulate
  lift→⇒ : {Δ : Tel} (A B : el Δ → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : (A δ₀) ⇒ (B δ₀)) →
    lift→ (λ w → (A w) ⇒ (B w)) δ₂ f₀ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒ {! -- Need to fill over a degenerate square in Δ
                            -- refl f₀ ⊙ a₀ ⊙ tr← A δ₂ a₁ ∙ (utr← A δ₂ a₁ a₀ (tr← A δ₂ a₁) a₂ (lift← A δ₂ a₁))
                            --lift→ B δ₂ (f₀ ∙ tr← A δ₂ a₁)!}
-}
