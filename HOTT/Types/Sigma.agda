{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Types.Sigma where

open import HOTT.Rewrite
open import HOTT.Identity

infixr 30 _,_ Σ
infixr 35 _×_

--------------------
-- Σ-types
--------------------

postulate
  Σ : (A : Type) (B : A → Type) → Type
  _,_ : {A : Type} {B : A → Type} (a : A) → B a → Σ A B

syntax Σ A (λ x → B) = （ x ⦂ A ）× B

postulate
  fst : {A : Type} {B : A → Type} → Σ A B → A
  snd : {A : Type} {B : A → Type} (u : Σ A B) → B (fst u)
  Ση : (A : Type) (B : A → Type) (u : Σ A B) → (fst u , snd u) ≡ u
  fstβ : {A : Type} {B : A → Type} (a : A) (b : B a) → fst {A} {B} (a , b) ≡ a

{-# REWRITE Ση fstβ #-}

postulate
  sndβ : {A : Type} {B : A → Type} (a : A) (b : B a) → snd {A} {B} (a , b) ≡ b

{-# REWRITE sndβ #-}

----------------------------------------
-- Non-dependent product types
----------------------------------------

_×_ : Type → Type → Type
A × B = （ _ ⦂ A ）× B
