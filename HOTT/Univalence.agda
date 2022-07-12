{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Univalence where

open import HOTT.Rewrite using (Type; _≡_; _≡ᵉ_; coe→; coe←)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Sigma.Base
open import HOTT.Universe.Base
open import HOTT.Groupoids

----------------------------------------
-- Bi-invertible maps
----------------------------------------

-- It might be better in principle to use half-adjoint equivalences,
-- but bi-invertible maps are easier to show to be a proposition.

BiInv : {A B : Type} (f : A ⇒ B) → Type
BiInv {A} {B} f = (Σ[ g ⦂ B ⇒ A ] g ∘ f ＝ idmap A) × (Σ[ h ⦂ B ⇒ A ] f ∘ h ＝ idmap B)

QInv→BiInv : {A B : Type} (f : A ⇒ B) → QInv f → BiInv f
QInv→BiInv f (g , sect , retr) = (g , sect) , (g , retr)

BiInv→QInv : {A B : Type} (f : A ⇒ B) → BiInv f → QInv f
BiInv→QInv {A} {B} f ((g , sect) , (h , retr)) = h ,
  (begin
     h ∘ f
   ＝⟨⟩
     idmap A ∘ h ∘ f
   ＝⟨ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ rev {A ⇒ A} {g ∘ f} sect ∙ (h ∙ (f ∙ a₀)) ∙ (h ∙ (f ∙ a₁)) ∙ (cong (h ∘ f) a₂)) ⟩
     g ∘ f ∘ h ∘ f
   ＝⟨ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ cong g (retr ∙ (f ∙ a₀) ∙ (f ∙ a₁) ∙ (cong f a₂))) ⟩
     g ∘ idmap B ∘ f
   ＝⟨⟩
     g ∘ f
   ＝⟨ sect ⟩
     idmap A
   ∎) , retr
