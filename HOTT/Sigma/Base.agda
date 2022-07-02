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
  IdΣ : {Δ : Tel} (A : el Δ → Type) (B : (x : el Δ) → A x → Type)
    (δ : el (ID Δ)) (u₀ : Σ (A (δ ₀)) (λ a → B (δ ₀) a))
                    (u₁ : Σ (A (δ ₁)) (λ a → B (δ ₁) a)) →
    Id {Δ} (Λ w ⇨ Σ (A w) (B w)) δ u₀ u₁ ≡
    Σ[ e ﹕ Id (Λ⇨ A) δ (fst u₀) (fst u₁) ]
      Id {Δ ▸ (Λ⇨ A)} (Λ x ⇨ B (pop x) (top x))
         (δ ∷ fst u₀ ∷ fst u₁ ∷ e) (snd u₀) (snd u₁)
  ＝Σ : (A : Type) (B : A → Type) (u₀ u₁ : Σ A B) →
    (u₀ ＝ u₁) ≡
    Σ[ e ﹕ (fst u₀ ＝ fst u₁) ]
    Id {ε▸ A} (Λ a ⇨ B (top a)) ([] ∷ fst u₀ ∷ fst u₁ ∷ e) (snd u₀) (snd u₁)

{-# REWRITE IdΣ ＝Σ #-}

postulate
  ap, : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type}
    (f : (δ : el Δ) → A δ) (g : (δ : el Δ) → B δ (f δ)) (δ : el (ID Δ)) →
    ap (Λ w ⇨ Σ (A w) (λ x → B w x)) (λ w → f w , g w) δ ≡
    (ap (Λ⇨ A) f δ ,
     ap ((Λ x ⇨ B (pop x) (top {Δ} {Λ x ⇨ A x} x)) ⊚ (Λ x ⇨ᵉ x ∷ f x)) g δ)
  refl, : {A : Type} {B : A → Type} (a : A) (b : B a) →
    refl {Σ A B} (a , b) ≡
    (refl a , coe→ (Id-AP (λ _ → [] ∷ a) [] (Λ x ⇨ B (top {ε} {Λ _ ⇨ A} x)) b b) (refl b))
  ap-fst : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type}
    (δ : el (ID Δ)) (u : (x : el Δ) → Σ (A x) (B x)) →
    ap (Λ⇨ A) (λ x → fst {A x} {λ y → B x y} (u x)) δ ≡
    fst (ap (Λ w ⇨ Σ (A w) (λ x → B w x)) u δ)
  refl-fst : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (fst {A} {B} u) ≡ fst (refl u)

{-# REWRITE ap, refl, ap-fst refl-fst #-}

postulate
  ap-snd : {Δ : Tel} {A : el Δ → Type} {B : (w : el Δ) → A w → Type}
    (δ : el (ID Δ)) (u : (x : el Δ) → Σ (A x) (B x)) →
    ap (Λ x ⇨ B x (fst (u x))) (λ x → snd (u x)) δ ≡
    coe← (Id-AP {Δ} {Δ ▸ Λ⇨ A} (λ x → x ∷ fst (u x)) δ
                (Λ w ⇨ B (pop w) (top w))
                (snd (u (δ ₀))) (snd (u (δ ₁))))
         (snd (ap (Λ x ⇨ Σ (A x) (B x)) u δ))
  refl-snd : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (snd u) ≡
    coe← (Id-AP (λ _ → [] ∷ fst u) [] (Λ x ⇨ B (top {ε} {Λ _ ⇨ A} x)) (snd u) (snd u))
          (snd (refl u))

{-# REWRITE ap-snd refl-snd #-}
