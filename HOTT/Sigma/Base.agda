{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sigma.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

--------------------
-- Σ-types
--------------------

postulate
  Σ : (A : Type) → (B : A → Type) → Type
  _﹐_ : {A : Type} {B : A → Type} (a : A) → B a → Σ A B
  π₁ : {A : Type} {B : A → Type} → Σ A B → A
  π₂ : {A : Type} {B : A → Type} (u : Σ A B) → B (π₁ u)

infix 30 _﹐_

syntax Σ A (λ x → B) = Σ[ x ﹕ A ] B

postulate
  βπ₁ : (A : Type) (B : A → Type) (a : A) (b : B a) → π₁ {B = B} (a ﹐ b) ≡ a

{-# REWRITE βπ₁ #-}

postulate
  βπ₂ : (A : Type) (B : A → Type) (a : A) (b : B a) → π₂ {B = B} (a ﹐ b) ≡ b
  η﹐ : (A : Type) (B : A → Type) (u : Σ A B) → (π₁ u ﹐ π₂ u) ≡ u

{-# REWRITE βπ₂ η﹐ #-}

postulate
  Id′Σ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (λ a → B (δ ₀) a)) (u₁ : Σ (A (δ ₁)) (λ a → B (δ ₁) a)) →
    Id′ {Δ} (λ w → Σ (A w) (B w)) δ u₀ u₁ ≡
    Σ[ e ﹕ Id′ A δ (π₁ u₀) (π₁ u₁) ] Id′ {Δ ▸ A} (uncurry B) (δ ∷ π₁ u₀ ∷ π₁ u₁ ∷ e) (π₂ u₀) (π₂ u₁)
  IdΣ : (A : Type) (B : A → Type) (u₀ u₁ : Σ A B) →
    Id (Σ A B) u₀ u₁ ≡
    Σ[ e ﹕ Id A (π₁ u₀) (π₁ u₁) ] Id′ {ε ▸ (λ _ → A)} (λ a → B (top a)) ([] ∷ π₁ u₀ ∷ π₁ u₁ ∷ e) (π₂ u₀) (π₂ u₁)

{-# REWRITE Id′Σ IdΣ #-}

postulate
  ap﹐ : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type} (f : (δ : el Δ) → A δ) (g : (δ : el Δ) → B δ (f δ))
    (δ : el (ID Δ)) →
    ap {A = λ w → Σ (A w) (B w)} (λ w → f w ﹐ g w) δ ≡
    (ap f δ ﹐  coe→ (Id′-AP (λ w → (w ∷ f w)) δ (uncurry B) _ _) (ap g δ))
  refl﹐ : {A : Type} {B : A → Type} (a : A) (b : B a) →
    refl {Σ A B} (a ﹐ b) ≡ (refl a ﹐ coe→ (Id′-AP {ε} (λ _ → [] ∷ a) [] (λ x → B (top x)) b b) (refl b))
  apπ₁ : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type} (δ : el (ID Δ))
    (u : (x : el Δ) → Σ (A x) (B x)) → ap (λ x → π₁ (u x)) δ ≡ π₁ (ap u δ)
  reflπ₁ : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (π₁ u) ≡ π₁ (refl u)

{-# REWRITE ap﹐ refl﹐ apπ₁ reflπ₁ #-}

-- Here we have to coerce explicitly, because matching for a rewrite would require rewriting some argument backwards.
postulate
  apπ₂ : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type} (δ : el (ID Δ))
    (u : (x : el Δ) → Σ (A x) (B x)) →
    ap (λ x → π₂ (u x)) δ ≡ coe← (Id′-AP (λ w → w ∷ π₁ (u w)) δ (uncurry B) _ _) (π₂ (ap u δ))
  reflπ₂ : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (π₂ u) ≡  coe← (Id′-AP {ε} (λ _ → [] ∷ π₁ u) [] (λ x → B (top x)) (π₂ u) (π₂ u)) (π₂ (refl u)) 

{-# REWRITE apπ₂ reflπ₂ #-}

postulate
  Id′-APΣ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ))
           (A : el Δ → Type) (B : (x : el Δ) → A x → Type)
           {u₀ : Σ (A (f (γ ₀))) (B (f (γ ₀)))} {u₁ : Σ (A (f (γ ₁))) (B (f (γ ₁)))} →
    Id′-AP f γ (λ w → Σ (A w) (B w)) u₀ u₁ ≡
      ≡ʰ→≡ (scong2dʰ Σ (Id′-AP f γ A (π₁ u₀) (π₁ u₁))
        (funextʰ (λ x₀ x₁ x₂ → ≡→≡ʰ
          (Id′-AP≡ (λ w → (f (pop w) ∷ top w)) (γ ∷ π₁ u₀ ∷ π₁ u₁ ∷ x₀)
            (∷≡ (λ u → Id′ A (pop (pop u)) (top (pop u)) (top u))
              {AP f γ ∷ π₁ u₀ ∷ π₁ u₁} {AP (λ z → f (pop z)) (γ ∷ π₁ u₀ ∷ π₁ u₁ ∷ x₀) ∷ π₁ u₀ ∷ π₁ u₁}
              (∷≡ (λ u → A (pop u ₁)) {AP f γ ∷ π₁ u₀} {AP (λ z → f (pop z)) (γ ∷ π₁ u₀ ∷ π₁ u₁ ∷ x₀) ∷ π₁ u₀}
                (∷≡ (λ u → A (u ₀)) {AP f γ} {AP (λ z → f (pop z)) (γ ∷ π₁ u₀ ∷ π₁ u₁ ∷ x₀)}
                  (AP-AP pop f (γ ∷ π₁ u₀ ∷ π₁ u₁ ∷ x₀))
                {π₁ u₀} {π₁ u₀} reflʰ)
              {π₁ u₁} {π₁ u₁} reflʰ)
            (revʰ (coe→≡ʰ (Id′-AP (λ z → f (pop z)) (γ ∷ π₁ u₀ ∷ π₁ u₁ ∷ x₀) A (π₁ u₀) (π₁ u₁))
                          (coe← (Id′-AP (λ x → pop x) (γ ∷ π₁ u₀ ∷ π₁ u₁ ∷ x₀) (λ z → A (f z)) (π₁ u₀) (π₁ u₁)) x₀)
                  •ʰ coe←≡ʰ (Id′-AP (λ x → pop x) (γ ∷ π₁ u₀ ∷ π₁ u₁ ∷ x₀) (λ z → A (f z)) (π₁ u₀) (π₁ u₁)) x₀
                  •ʰ x₂)))
          (uncurry B) reflʰ reflʰ))))

{-# REWRITE Id′-APΣ #-}

-- TODO: Compute ap-AP on ﹐ and π₁ and π₂
