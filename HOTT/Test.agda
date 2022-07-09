{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Test where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Groupoids
open import HOTT.Pi
open import HOTT.Sigma
open import HOTT.Copy
open import HOTT.Universe
open import HOTT.Bool

----------------------------------------
-- Testing normalization of ap-top
----------------------------------------

postulate
  A : Type
  a₀ a₁ : A
  a₂ : a₀ ＝ a₁

postulate
  B : (ε▸ A) ⇨ Type
  b₀ : B ⊘ ([] ∷ a₀)
  b₁ : B ⊘ ([] ∷ a₁)
  b₂ : Id B ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁
  C : ((ε▸ A) ▸ B) ⇨ Type
  c₀ : C ⊘ ([] ∷ a₀ ∷ b₀)
  c₁ : C ⊘ ([] ∷ a₁ ∷ b₁)
  c₂ : Id C ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂) c₀ c₁

--Normalize these with C-c C-n
egA-A = ap {ε▸ A} ((Λ _ ⇨ A) ⊚ POP) (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂)
egAB-A = ap {(ε▸ A) ▸ B} ((Λ _ ⇨ A) ⊚ POP ⊚ᵉ POP) (λ w → top (pop w)) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂)
egABC-A = ap {(ε▸ A) ▸ B ▸ C} ((Λ _ ⇨ A) ⊚ POP ⊚ᵉ POP ⊚ᵉ POP) (λ w → top (pop (pop w))) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)
egAB-B = ap {(ε▸ A) ▸ B} (B ⊚ POP) (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂)
egABC-B = ap {(ε▸ A) ▸ B ▸ C} (B ⊚ POP ⊚ᵉ POP) (λ w → top (pop w)) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)
egABC-C = ap {(ε▸ A) ▸ B ▸ C} (C ⊚ POP) (λ w → top w) ([] ∷ a₀ ∷ a₁ ∷ a₂ ∷ b₀ ∷ b₁ ∷ b₂ ∷ c₀ ∷ c₁ ∷ c₂)

------------------------------
-- Definitional univalence
------------------------------

-- We check that both a function and its inverse are preserved
-- definitionally by passing through univalence.

coe⇒ua : {A B : Type} (f : A ⇒ B) (qf : QInv f) →
  coe⇒ (ua f qf) ≡ f
coe⇒ua f qf = reflᵉ

coe⇐ua : {A B : Type} (f : A ⇒ B) (g : B ⇒ A)
  (sect : g ∘ f ＝ idmap A) (retr : f ∘ g ＝ idmap B) →
  coe⇐ (ua f (g , sect , retr)) ≡ g
coe⇐ua f g sect retr = reflᵉ

------------------------------
-- Coercion along negation
------------------------------

-- We make the negation (flip) automorphism of bool into an
-- identification in the universe, and check that coercing along it
-- computes to the correct result.  This is some small amount of
-- evidence that we can hope for canonicity.

＝¬ : 𝟚 ＝ 𝟚
＝¬ = ua ¬ QInv-¬

coe⇒¬ : coe⇒ ＝¬ ∙ true ≡ false
coe⇒¬ = reflᵉ

coe⇐¬ : coe⇐ ＝¬ ∙ true ≡ false
coe⇐¬ = reflᵉ
