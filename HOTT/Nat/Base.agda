{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Nat.Base where

import Agda.Builtin.Nat

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Unit
open import HOTT.Pi.Base
open import HOTT.Sigma.Base

infix 35 _+ℕ_ _*ℕ_

----------------------------------------
-- Generalized Natural numbers
----------------------------------------

data nat (Ω : Type) (ζ : Ω) (σ : Ω → Ω) : Ω → Type where
  Z : nat Ω ζ σ ζ
  S : {x : Ω} → nat Ω ζ σ x → nat Ω ζ σ (σ x)

rec : {Ω : Type} {ζ : Ω} {σ : Ω → Ω}
  {ω : Ω} (n : nat Ω ζ σ ω)
  (C : (x : Ω) → nat Ω ζ σ x → Type)
  (fzero : C ζ Z)
  (fsuc : (x : Ω) (n : nat Ω ζ σ x) → C x n → C (σ x) (S n))
  → C ω n
rec Z C fzero fsuc = fzero
rec (S n) C fzero fsuc = fsuc _ _ (rec n C fzero fsuc)

ℕ : Type
ℕ = nat ⊤ ★ (λ _ → ★) ★

----------------------------------------
-- Pretty input and output
----------------------------------------

record Number {a} (A : Set a) : Set a where
  field fromNat : Agda.Builtin.Nat.Nat → A

open Number {{...}} public

Nat→ℕ : Agda.Builtin.Nat.Nat → ℕ
Nat→ℕ Agda.Builtin.Nat.zero = Z
Nat→ℕ (Agda.Builtin.Nat.suc n) = S (Nat→ℕ n)

instance
  ℕ-Number : Number ℕ
  Number.fromNat ℕ-Number = Nat→ℕ

{-# BUILTIN FROMNAT fromNat #-}

show : ℕ → Agda.Builtin.Nat.Nat
show Z = Agda.Builtin.Nat.zero
show (S n) = Agda.Builtin.Nat.suc (show n)

------------------------------
-- Arithmetic
------------------------------

_+ℕ_ : ℕ → ℕ → ℕ
m +ℕ n = rec m _ n (λ _ m m+n → S (m+n))

_*ℕ_ : ℕ → ℕ → ℕ
m *ℕ n = rec m _ Z (λ _ m m*n → n +ℕ m*n)

-- TODO: This should also be provable by computing ＝ℕ
+ℕ0 : (x : ℕ) → x +ℕ 0 ＝ x
+ℕ0 Z = refl Z
+ℕ0 (S x) = refl (ƛ n ⇒ S n) ∙ (x +ℕ 0) ∙ x ∙ (+ℕ0 x)
