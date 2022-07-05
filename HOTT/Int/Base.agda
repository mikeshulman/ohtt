{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Int.Base where

import Agda.Builtin.Nat
import Agda.Builtin.Int

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Unit
open import HOTT.Sigma.Base
open import HOTT.Nat

----------------------------------------
-- Integers
----------------------------------------

data int (Ω : Type) {N : Type} (ν : N → Ω) (ζ : Ω) (ψ : N → Ω) : Ω → Type where
  neg : (n : N) → int Ω ν ζ ψ (ν n)
  zero : int Ω ν ζ ψ ζ
  pos : (n : N) → int Ω ν ζ ψ (ψ n)

intcase : {Ω : Type} {N : Type} {ν : N → Ω} {ζ : Ω} {ψ : N → Ω}
  {ω : Ω} (z : int Ω ν ζ ψ ω)
  (C : (x : Ω) → int Ω ν ζ ψ x → Type)
  (fneg : (n : N) → C (ν n) (neg n))
  (fzero : C ζ zero)
  (fpos : (n : N) → C (ψ n) (pos n))
  → C ω z
intcase (neg n) C fneg fzero fpos = fneg n
intcase (zero) C fneg fzero fpos = fzero
intcase (pos n) C fneg fzero fpos = fpos n

ℤ : Type
ℤ = int ⊤ {ℕ} (λ _ → ★) ★ (λ _ → ★) ★

ι : ℕ → ℤ
ι Z = zero
ι (S n) = pos n

----------------------------------------
-- Pretty input and output
----------------------------------------

instance
  ℤ-Number : Number ℤ
  Number.fromNat ℤ-Number Agda.Builtin.Nat.zero = zero
  Number.fromNat ℤ-Number (Agda.Builtin.Nat.suc n) = pos (Nat→ℕ n)

fromNeg : Agda.Builtin.Nat.Nat → ℤ
fromNeg Agda.Builtin.Nat.zero = zero
fromNeg (Agda.Builtin.Nat.suc n) = neg (Nat→ℕ n)

{-# BUILTIN FROMNEG fromNeg #-}

------------------------------
-- Arithmetic
------------------------------

ℤsuc : ℤ → ℤ
ℤsuc z = intcase z _ (λ n → rec n _ zero (λ _ n' _ → (neg n'))) (pos Z) (λ n → pos (S n))
