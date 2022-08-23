{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Decidable where

open import HOTT.Rewrite using (Type; _≡_; coe→; coe←)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Sigma.Base
open import HOTT.Groupoids
open import HOTT.Sum.Base
open import HOTT.Empty

-- I don't know why so many arguments have to be given explicitly here.
rijke : {A : Type} (R : A → A → Type) (Rprp : (x y : A) → isProp (R x y))
  (ρ : (x : A) → R x x) (f : Π[ x ⦂ A ] Π[ y ⦂ A ] R x y ⇒ x ＝ y) → isSet A
rijke {A} R Rprp ρ f = K→isSet λ x p →
  begin
    refl {A} x
  ＝⟨ rev {x ＝ x} (rev⊙ {A} {x} {x} (f ∙ x ∙ x ∙ ρ x)) ⟩
    _⊙_ {A} {x} {x} {x} (rev {A} {x} {x} (f ∙ x ∙ x ∙ ρ x)) (f ∙ x ∙ x ∙ ρ x)
  ＝⟨ cong (ƛ q ⇒ _⊙_ {A} {x} {x} {x} (rev {A} {x} {x} (f ∙ x ∙ x ∙ ρ x)) q) {f ∙ x ∙ x ∙ ρ x} {_⊙_ {A} {x} {x} {x} (f ∙ x ∙ x ∙ ρ x) p}
          (utr→ (Id/ (Λ _ ⇨ A)) ([] ∷ x ∷ x ∷ refl x ∷ x ∷ x ∷ p) (f ∙ x ∙ x ∙ ρ x)
                (f ∙ x ∙ x ∙ ρ x) (_⊙_ {A} {x} {x} {x} (f ∙ x ∙ x ∙ ρ x) p)
                (coe→ (Id-AP {ε ▸ (Λ _ ⇨ A) ▸ (Λ z ⇨ R x (top z))} {ID▸▸ (Λ _ ⇨ A)} (λ w → [] ∷ x ∷ top (pop w))
                             ([] ∷ x ∷ x ∷ p ∷ ρ x ∷ ρ x ∷ Id-prop p (R x) (Rprp x) (ρ x) (ρ x)) (Id/ (Λ _ ⇨ A))
                             (f ∙ x ∙ x ∙ ρ x) (f ∙ x ∙ x ∙ ρ x))
                      (refl (f ∙ x) ∙ x ∙ x ∙ p ∙ (ρ x) ∙ (ρ x) ∙ Id-prop p (R x) (Rprp x) (ρ x) (ρ x)))
                (fill→ (Λ _ ⇨ A) [] (refl x) p (f ∙ x ∙ x ∙ ρ x))) ⟩
    _⊙_ {A} {x} {x} {x} (rev {A} {x} {x} (f ∙ x ∙ x ∙ ρ x)) (_⊙_ {A} {x} {x} {x} (f ∙ x ∙ x ∙ ρ x) p)
  ＝⟨ rev {x ＝ x} (⊙assoc {A} {x} {x} {x} {x} (rev {A} {x} {x} (f ∙ x ∙ x ∙ ρ x)) (f ∙ x ∙ x ∙ ρ x) p) ⟩
    _⊙_ {A} {x} {x} {x} (_⊙_ {A} {x} {x} {x}  (rev {A} {x} {x} (f ∙ x ∙ x ∙ ρ x)) (f ∙ x ∙ x ∙ ρ x)) p
  ＝⟨ cong {x ＝ x} (ƛ q ⇒ _⊙_ {A} {x} {x} {x} q p) (rev⊙ {A} {x} {x} (f ∙ x ∙ x ∙ ρ x)) ⟩
    _⊙_ {A} {x} {x} {x} (refl {A} x) p
  ＝⟨ refl⊙ {A} {x} {x} p ⟩
    p
  ∎

DecEq : Type → Type
DecEq A = Π[ x ⦂ A ] Π[ y ⦂ A ] (x ＝ y) ⊎ ((x ＝ y) ⇒ ⊥)

-- Hedberg's theorem: a type with decidable equality is a set
hedberg : {A : Type} (dec : DecEq A) → isSet A
hedberg dec = rijke (λ x y → ((x ＝ y) ⇒ ⊥) ⇒ ⊥)
  (λ x y → ƛ f ⇒ ƛ g ⇒  ƛ p ⇒ ⊥-elim (λ s → Π[ q ⦂ (x ＝ y) ⇒ ⊥ ] Π[ r ⦂ p ＝ q ] f ∙ p ＝ g ∙ q) (g ∙ p))
  (λ x → ƛ f ⇒ f ∙ (refl x))
  (ƛ x ⇒ ƛ y ⇒ ƛ f ⇒ case (dec ∙ x ∙ y) (λ _ _ → x ＝ y) (λ p → p) (λ q → ⊥-elim (λ _ → x ＝ y) (f ∙ q)))
