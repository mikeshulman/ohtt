{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Arrow where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
-- open import HOTT.Square
-- open import HOTT.Square.Degenerate
-- open import HOTT.Fill
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
    (δ : el (ID Δ)) (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) (f₁ : (A (δ ₁)) ⇒ (B (δ ₁))) →
    Id′ (λ w → (A w) ⇒ (B w)) δ f₀ f₁ ≡
      Π (A (δ ₀)) (λ a₀ →
      Π (A (δ ₁)) (λ a₁ →
      (Id′ A δ a₀ a₁) ⇒
        Id′ B δ (f₀ ∙ a₀) (f₁ ∙ a₁)))
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
  apΛ⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ)) (f : (x : el Δ) → A x → B x) →
    ap (λ x → Λ y ⇒ f x y) δ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒  coe→ (Id′-AP {Δ ▸ A} pop (δ ∷ a₀ ∷ a₁ ∷ a₂) B (f (δ ₀) a₀) (f (δ ₁) a₁))
                                 (ap (λ w → f (pop w) (top w)) (δ ∷ a₀ ∷ a₁ ∷ a₂))  
  reflΛ⇒ : (A B : Type) (f : A → B) →
    refl (Λ x ⇒ f x) ≡ Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒ ap {ε ▸ (λ _ → A)} (λ x → f (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂)
  ap∙ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f : (x : el Δ) → (A x) ⇒ (B x)) (a : (x : el Δ) → A x) →
    ap (λ x → f x ∙ a x) δ ≡ (ap f δ ⊙ (a (δ ₀)) ⊙ (a (δ ₁)) ∙ (ap a δ))
  refl∙ : (A B : Type) (f : A ⇒ B) (a : A) →
    refl (f ∙ a) ≡ (refl f ⊙ a ⊙ a ∙ (refl a))

{-# REWRITE apΛ⇒ reflΛ⇒ ap∙ refl∙ #-}

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

-- However, lift→ and lift← are VASTLY simpler, in particular not requiring sq▸.

-- TODO: These require squares and fillers.

{-

postulate
  lift→⇒ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) →
    lift→ (λ w → (A w) ⇒ (B w)) δ f₀ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒ comp↓ B δ δ (REFL (δ ₀)) (REFL (δ ₁)) (DEGSQ-TB Δ δ)
                                (lift→ B δ (f₀ ∙ tr← A δ a₁))
                                (refl f₀ ⊙ a₀ ⊙ tr← A δ a₁ ∙ (utr← A δ a₁ a₀ (tr← A δ a₁) a₂ (lift← A δ a₁)))
                                (refl (tr→ B δ (f₀ ∙ tr← A δ a₁)))
  lift←⇒ : {Δ : Tel} (A B : el Δ → Type)
    (δ : el (ID Δ)) (f₁ : (A (δ ₁)) ⇒ (B (δ ₁))) →
    lift← (λ w → (A w) ⇒ (B w)) δ f₁ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒ comp↓ B δ δ (REFL (δ ₀)) (REFL (δ ₁)) (DEGSQ-TB Δ δ)
                                (lift← B δ (f₁ ∙ tr→ A δ a₀))
                                (refl (tr← B δ (f₁ ∙ tr→ A δ a₀)))
                                (refl f₁ ⊙ a₁ ⊙ tr→ A δ a₀ ∙ (utr→ A δ a₀ a₁ (tr→ A δ a₀) a₂ (lift→ A δ a₀)))

{-# REWRITE lift→⇒ lift←⇒ #-}

postulate
  utr→⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) (f₁ f₁' : (A (δ ₁)) ⇒ (B (δ ₁))) (f₂ : Id′ (λ w → A w ⇒ B w) δ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ f₀ f₁') →
    utr→ (λ w → (A w) ⇒ (B w)) δ f₀ f₁ f₁' f₂ f₂' ≡
    Λ a₁ ⇛ Λ a₁' ⇛ Λ a₂ ⇒
     comp→ B δ δ (REFL (δ ₀)) (REFL (δ ₁)) (DEGSQ-TB Δ δ)
            (f₂ ⊙ (tr← A δ a₁) ⊙ a₁ ∙ (lift← A δ a₁))
            (f₂' ⊙ (tr← A δ a₁') ⊙ a₁' ∙ (lift← A δ a₁'))
            (ap {ε ▸ (λ _ → A (δ ₁))} (λ x → f₀ ∙ tr← A δ (top x)) ([] ∷ a₁ ∷ a₁' ∷ a₂))
  utr←⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f₁ : (A (δ ₁)) ⇒ (B (δ ₁))) (f₀ f₀' : (A (δ ₀)) ⇒ (B (δ ₀))) (f₂ : Id′ (λ w → A w ⇒ B w) δ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ f₀' f₁) →
    utr← (λ w → (A w) ⇒ (B w)) δ f₁ f₀ f₀' f₂ f₂' ≡
    Λ a₀ ⇛ Λ a₀' ⇛ Λ a₂ ⇒
     comp← B δ δ (REFL (δ ₀)) (REFL (δ ₁)) (DEGSQ-TB Δ δ)
            (f₂ ⊙ a₀ ⊙ (tr→ A δ a₀) ∙ (lift→ A δ a₀))
            (f₂' ⊙ a₀' ⊙ (tr→ A δ a₀') ∙ (lift→ A δ a₀'))
            (ap {ε ▸ (λ _ → A (δ ₀))} (λ x → f₁ ∙ tr→ A δ (top x)) ([] ∷ a₀ ∷ a₀' ∷ a₂))

{-# REWRITE utr→⇒ utr←⇒ #-}

-}

{-
postulate
  ulift→⇒ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
    (f₀ : (A (δ ₀)) ⇒ (B (δ ₀))) (f₁ f₁' : (A (δ ₁)) ⇒ (B (δ ₁))) (f₂ : Id′ (λ w → A w ⇒ B w) δ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ f₀ f₁') →
    ulift→ (λ w → (A w) ⇒ (B w)) δ f₀ f₁ f₁' f₂ f₂' ≡
    Λ a₀₀ ⇛ Λ a₁₀ ⇛ Λ a₂₀ ⇛ Λ a₀₁ ⇛ Λ a₁₁ ⇛ Λ a₂₁ ⇛ Λ a₀₂ ⇛ Λ a₁₂ ⇛ Λ a₂₂ ⇒
      {!!} -- This looks like it might start to get into 3-cube territory.
-}
