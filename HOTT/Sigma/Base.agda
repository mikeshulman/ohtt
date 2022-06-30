{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-projection-like #-}

module HOTT.Sigma.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl

--------------------
-- Σ-types
--------------------

data Σ (A : Type) (B : A → Type) : Type where
  _,_ : (a : A) → B a → Σ A B
open Σ

infixr 30 _,_ Σ
syntax Σ A (λ x → B) = Σ[ x ﹕ A ] B

infixr 30 _×_

_×_ : Type → Type → Type
A × B = Σ[ x ﹕ A ] B

fst : {A : Type} {B : A → Type} → Σ A B → A
fst (a , b) = a

snd : {A : Type} {B : A → Type} (u : Σ A B) → B (fst u)
snd (a , b) = b

postulate
  η, : (A : Type) (B : A → Type) (u : Σ A B) → (fst u , snd u) ≡ u

{-# REWRITE η, #-}

postulate
  IdΣ : {Δ : Tel} (A : el Δ → Type) (B : (w : el Δ) → A w → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (λ a → B (δ ₀) a)) (u₁ : Σ (A (δ ₁)) (λ a → B (δ ₁) a)) →
    Id {Δ} (Λ w ⇒ Σ (A w) (B w)) δ u₀ u₁ ≡
    Σ[ e ﹕ Id (Λ x ⇒ A x) δ (fst u₀) (fst u₁) ] Id {Δ ▸ (Λ x ⇒ A x)} (Λ x ⇒ uncurry B x) (δ ∷ fst u₀ ∷ fst u₁ ∷ e) (snd u₀) (snd u₁)
  ＝Σ : (A : Type) (B : A → Type) (u₀ u₁ : Σ A B) →
    (u₀ ＝ u₁) ≡
    Σ[ e ﹕ (fst u₀ ＝ fst u₁) ] Id {ε ▸ (Λ _ ⇒ A)} (Λ a ⇒ B (top a)) ([] ∷ fst u₀ ∷ fst u₁ ∷ e) (snd u₀) (snd u₁)

{-# REWRITE IdΣ ＝Σ #-}

postulate
  ap, : {Δ : Tel} {A : Δ →Type} {B : (Δ ▸ A) →Type}
    (f : (δ : el Δ) → A ⊘ δ) (g : (δ : el Δ) → B ⊘ (δ ∷ f δ))
    (δ : el (ID Δ)) →
    ap (Λ w ⇒ Σ (A ⊘ w) (λ x → B ⊘ (w ∷ x))) (λ w → f w , g w) δ ≡
    (ap A f δ , ap (B ⊚ (Λ x ⇨ _∷_ {B = A} x (f x))) g δ)
  refl, : {A : Type} {B : A → Type} (a : A) (b : B a) →
    refl {Σ A B} (a , b) ≡ (refl a ,  {!refl b!})
{-
  ap-fst : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type} (δ : el (ID Δ)) (u : (x : el Δ) → Σ (A x) (B x)) →
    ap (λ x → fst {A x} {λ y → B x y} (u x)) δ ≡ fst (ap u δ)
  refl-fst : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (fst {A} {B} u) ≡ fst (refl u)

{-# REWRITE ap, refl, ap-fst refl-fst #-}

postulate
  ap-snd : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type} (δ : el (ID Δ))
    (u : (x : el Δ) → Σ (A x) (B x)) →
    ap (λ x → snd (u x)) δ ≡
    {!coe→ (Id-AP▸ A (λ x → x) (λ x → fst (u x)) δ
                   (λ w → B (pop w) (top w)) (snd (u (δ ₀))) (snd (u (δ ₁))))
         (snd (ap u δ))!}
  refl-snd : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (snd u) ≡
    {!coe→ (Id-REFL[]▸ (λ _ → A) (λ x → B (top x)) (fst u) (snd u) (snd u))
          (snd (refl u))!}

{-# REWRITE ap-snd refl-snd #-}
-}
