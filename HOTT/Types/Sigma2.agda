{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Types.Sigma2 where

open import HOTT.Rewrite
open import HOTT.Identity
open import HOTT.Telescope
open import HOTT.Types.Pi
open import HOTT.Types.Sigma
open import HOTT.Types.Universe
open import HOTT.Types.Pi2

--------------------------------------------------
-- Identity types of dependent Σ-types
--------------------------------------------------

postulate
  ＝Σ : (A : Type) (B : A → Type) (u v : Σ A B) →
    (u ＝ v) ≡ （ p ⦂ fst u ＝ fst v ）× Id (ƛ x ⇒ B x) p (snd u) (snd v)

{-# REWRITE ＝Σ #-}

-- This computes as expected in the non-dependent case
＝× : (A B : Type) (u v : A × B) → (u ＝ v) ≡ ((fst u ＝ fst v) × (snd u ＝ snd v))
＝× A B u v = reflᵉ

-- In the RHS of "refl," we want to write (refl b).  That is well-typed
-- when B belongs to the object-level function-type (A ⇒ Type),
-- because in that case the type (_＝_ {B ∙ a} b b) of (refl b)
-- computes ("backwards") to what's expected.  But since we want "refl,"
-- to fire on arbitrary Σ-types, which we had to define as
-- parametrized by a framework-level function-type, we can't just
-- write (refl b).  Instead we prove a lemma that frobnicates (refl b)
-- to have the correct type for an object-level function-type, then
-- call it with an abstracted argument.
frob-refl : {A : Type} (B : A ⇒ Type) (a : A) (b : B ∙ a) →
  (refl (𝚲 (λ x → B ∙ (top {ε} {Λ _ ⇨ A} x))) ⊘ ([] ∷ a ∷ a ∷ refl a)) // b ~ b
frob-refl B a b = refl b

postulate
  refl, : (A : Type) (B : A → Type) (a : A) (b : B a) → refl {Σ A B} (a , b) ≡ (refl a , frob-refl (𝛌 B) a b)
  refl-fst : (A : Type) (B : A → Type) (u : Σ A B) → refl (fst u) ≡ fst (refl u)

{-# REWRITE refl, refl-fst #-}

frob-refl-snd : {A : Type} (B : A ⇒ Type) (u : （ x ⦂ A ）× B ∙ x) → snd u ＝ snd u
frob-refl-snd B u = {!snd (refl u)!}

postulate
  refl-snd : (A : Type) (B : A → Type) (u : Σ A B) → refl (snd u) ≡ {!snd (refl u)!}


----------------------------------------
-- Identity types of eliminators
----------------------------------------

postulate
  ＝fst : (P : Type → Type) (B : Σ Type P) (b₀ b₁ : fst B) → (b₀ ＝ b₁) ≡ (fst (refl B) // b₀ ~ b₁)
  ＝snd : {A : Type} (B : A × Type) (b₀ b₁ : snd B) → (b₀ ＝ b₁) ≡ (snd (refl B) // b₀ ~ b₁)

{-# REWRITE ＝fst ＝snd #-}
