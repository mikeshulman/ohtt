{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Universe.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Sigma
open import HOTT.Pi
open import HOTT.Copy
open import HOTT.Groupoids

----------------------------------------
-- Identity types of the universe
----------------------------------------

postulate
  ＝U : (A B : Type) → (A ＝ B) ≡ Copy (11Corr A B)

{-# REWRITE ＝U #-}

-- Univalence for quasi-inverses.
ua : {A B : Type} (f : A ⇒ B) (qf : QInv f) → (A ＝ B)
ua f qf = QInv→11 f qf ↑

-- The inverse of univalence: coercion along an identification of types.
coe⇒ : {A B : Type} → (A ＝ B) → (A ⇒ B)
coe⇒ e = ƛ x ⇒ fst (fst (fst (snd (e ↓)) ∙ x))

coe⇐ : {A B : Type} → (A ＝ B) → (B ⇒ A)
coe⇐ e = ƛ y ⇒ fst (fst (snd (snd (e ↓)) ∙ y))

postulate
  apU : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) →
    (ap (Λ _ ⇨ Type) A δ) ↓ ≡
    ((ƛ a₀ ⇒ ƛ a₁ ⇒ Id (Λ⇨ A) δ a₀ a₁) ,
    ((ƛ a₀ ⇒ (tr→ (Λ⇨ A) δ a₀ , lift→ (Λ⇨ A) δ a₀) ,
              (ƛ x ⇒ ƛ x' ⇒ (utr→ (Λ⇨ A) δ a₀ (fst x) (fst x') (snd x) (snd x') ,
                             ulift→ (Λ⇨ A) δ a₀ (fst x) (fst x') (snd x) (snd x')))) ,
     (ƛ a₁ ⇒ (tr← (Λ⇨ A) δ a₁ , lift← (Λ⇨ A) δ a₁) ,
              (ƛ x ⇒ ƛ x' ⇒ (utr← (Λ⇨ A) δ a₁ (fst x) (fst x') (snd x) (snd x') ,
                             ulift← (Λ⇨ A) δ a₁ (fst x) (fst x') (snd x) (snd x'))))))

{-# REWRITE apU #-}

----------------------------------------
-- Identity types of type variables
----------------------------------------

-- Id-top, below, depends for its well-typedness on top-pop-pop-AP and
-- top-pop-AP applied at a constant family on the universe.  But even
-- top-pop-pop-AP-const doesn't help, because ＝U reduces even
-- further.  So we declare some additional special rewrites.  (This
-- same problem would happen with any other use of top-pop-pop-AP and
-- top-pop-AP at a particular type, but this is the only place so far
-- where we've needed such a thing.)
postulate
  top-pop-pop-AP-const-U : {Γ Δ : Tel} (f : Γ ⇨ᵉ el (Δ ▸ (Λ _ ⇨ Type))) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ top (f ⊘ᵉ (γ ₀))
  top-pop-AP-const-U : {Γ Δ : Tel} (f : Γ ⇨ᵉ el (Δ ▸ (Λ _ ⇨ Type))) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ top (f ⊘ᵉ (γ ₁))

{-# REWRITE top-pop-pop-AP-const-U top-pop-AP-const-U #-}

postulate
  Id-top : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el (Δ ▸ (Λ _ ⇨ Type)))
    (x₀ : top (f (γ ₀))) (x₁ : top (f (γ ₁))) →
    Id (Λ x ⇨ top (f x)) γ x₀ x₁ ≡
    fst (top (AP (Λ⇨ᵉ f) γ) ↓) ∙ x₀ ∙ x₁

{-# REWRITE Id-top #-}
