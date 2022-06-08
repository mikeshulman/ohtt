{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Arrow where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Transport
open import HOTT.Square
open import HOTT.Square.Degenerate
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

-- tr→ and tr← are only slightly simpler in the non-dependent case.
postulate
  tr→⇒ : {Δ : Tel} (A B : el Δ → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : (A δ₀) ⇒ (B δ₀)) →
    tr→ (λ w → (A w) ⇒ (B w)) δ₂ f₀ ≡ Λ a₁ ⇒ tr→ B {δ₀} {δ₁} δ₂ (f₀ ∙ (tr← A δ₂ a₁))
  tr←⇒ : {Δ : Tel} (A B : el Δ → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₁ : (A δ₁) ⇒ (B δ₁)) →
    tr← (λ w → (A w) ⇒ (B w)) δ₂ f₁ ≡ Λ a₀ ⇒ tr← B {δ₀} {δ₁} δ₂ (f₁ ∙ (tr→ A δ₂ a₀))

{-# REWRITE tr→⇒ tr←⇒ #-}

-- However, lift→ and lift← are VASTLY simpler, in particular not requiring sq▸.
postulate
  lift→⇒ : {Δ : Tel} (A B : el Δ → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : (A δ₀) ⇒ (B δ₀)) →
    lift→ (λ w → (A w) ⇒ (B w)) δ₂ f₀ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒ comp↓ B δ₂ δ₂ (REFL δ₀) (REFL δ₁) (DEGSQ-TB Δ δ₂)
                                (lift→ B δ₂ (f₀ ∙ tr← A δ₂ a₁))
                                (refl f₀ ⊙ a₀ ⊙ tr← A δ₂ a₁ ∙ (utr← A δ₂ a₁ a₀ (tr← A δ₂ a₁) a₂ (lift← A δ₂ a₁)))
                                (refl (tr→ B δ₂ (f₀ ∙ tr← A δ₂ a₁)))
  lift←⇒ : {Δ : Tel} (A B : el Δ → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₁ : (A δ₁) ⇒ (B δ₁)) →
    lift← (λ w → (A w) ⇒ (B w)) δ₂ f₁ ≡
    Λ a₀ ⇛ Λ a₁ ⇛ Λ a₂ ⇒ comp↓ B δ₂ δ₂ (REFL δ₀) (REFL δ₁) (DEGSQ-TB Δ δ₂)
                                (lift← B δ₂ (f₁ ∙ tr→ A δ₂ a₀))
                                (refl (tr← B δ₂ (f₁ ∙ tr→ A δ₂ a₀)))
                                (refl f₁ ⊙ a₁ ⊙ tr→ A δ₂ a₀ ∙ (utr→ A δ₂ a₀ a₁ (tr→ A δ₂ a₀) a₂ (lift→ A δ₂ a₀)))

{-# REWRITE lift→⇒ lift←⇒ #-}

postulate
  utr→⇒ : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (f₀ : (A δ₀) ⇒ (B δ₀)) (f₁ f₁' : (A δ₁) ⇒ (B δ₁)) (f₂ : Id′ (λ w → A w ⇒ B w) δ₂ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ₂ f₀ f₁') →
    utr→ (λ w → (A w) ⇒ (B w)) δ₂ f₀ f₁ f₁' f₂ f₂' ≡
    Λ a₁ ⇛ Λ a₁' ⇛ Λ a₂ ⇒
     comp→ B δ₂ δ₂ (REFL δ₀) (REFL δ₁) (DEGSQ-TB Δ δ₂)
            (f₂ ⊙ (tr← A δ₂ a₁) ⊙ a₁ ∙ (lift← A δ₂ a₁))
            (f₂' ⊙ (tr← A δ₂ a₁') ⊙ a₁' ∙ (lift← A δ₂ a₁'))
            (ap {ε ▸ (λ _ → A δ₁)} (λ x → f₀ ∙ tr← A δ₂ (top x)) {[] ∷ a₁} {[] ∷ a₁'} ([] ∷ a₂))
  utr←⇒ : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (f₁ : (A δ₁) ⇒ (B δ₁)) (f₀ f₀' : (A δ₀) ⇒ (B δ₀)) (f₂ : Id′ (λ w → A w ⇒ B w) δ₂ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ₂ f₀' f₁) →
    utr← (λ w → (A w) ⇒ (B w)) δ₂ f₁ f₀ f₀' f₂ f₂' ≡
    Λ a₀ ⇛ Λ a₀' ⇛ Λ a₂ ⇒
     comp← B δ₂ δ₂ (REFL δ₀) (REFL δ₁) (DEGSQ-TB Δ δ₂)
            (f₂ ⊙ a₀ ⊙ (tr→ A δ₂ a₀) ∙ (lift→ A δ₂ a₀))
            (f₂' ⊙ a₀' ⊙ (tr→ A δ₂ a₀') ∙ (lift→ A δ₂ a₀'))
            (ap {ε ▸ (λ _ → A δ₀)} (λ x → f₁ ∙ tr→ A δ₂ (top x)) {[] ∷ a₀} {[] ∷ a₀'} ([] ∷ a₂))

{-# REWRITE utr→⇒ utr←⇒ #-}

{-
postulate
  ulift→⇒ : {Δ : Tel} (A B : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (f₀ : (A δ₀) ⇒ (B δ₀)) (f₁ f₁' : (A δ₁) ⇒ (B δ₁)) (f₂ : Id′ (λ w → A w ⇒ B w) δ₂ f₀ f₁) (f₂' : Id′ (λ w → A w ⇒ B w) δ₂ f₀ f₁') →
    ulift→ (λ w → (A w) ⇒ (B w)) δ₂ f₀ f₁ f₁' f₂ f₂' ≡
    Λ a₀₀ ⇛ Λ a₁₀ ⇛ Λ a₂₀ ⇛ Λ a₀₁ ⇛ Λ a₁₁ ⇛ Λ a₂₁ ⇛ Λ a₀₂ ⇛ Λ a₁₂ ⇛ Λ a₂₂ ⇒
      {!!} -- This looks like it might start to get into 3-cube territory.
-}
