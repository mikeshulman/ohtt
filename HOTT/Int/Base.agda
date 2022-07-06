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
open import HOTT.Indices

----------------------------------------
-- Generalized integers
----------------------------------------

data int (Ω : Type) {N : Type} (ν : N → Ω) (ζ : Ω) (ψ : N → Ω) : Ω → Type where
  neg : (n : N) → int Ω ν ζ ψ (ν n)
  zero : int Ω ν ζ ψ ζ
  pos : (n : N) → int Ω ν ζ ψ (ψ n)

int-case : {Ω : Type} {N : Type} {ν : N → Ω} {ζ : Ω} {ψ : N → Ω} {ω : Ω}
  (C : (x : Ω) → int Ω ν ζ ψ x → Type)
  (fneg : (n : N) → C (ν n) (neg n))
  (fzero : C ζ zero)
  (fpos : (n : N) → C (ψ n) (pos n))
  (z : int Ω ν ζ ψ ω)
  → C ω z
int-case C fneg fzero fpos (neg n) = fneg n
int-case C fneg fzero fpos zero = fzero
int-case C fneg fzero fpos (pos n) = fpos n

------------------------------
-- Ordinary integers
------------------------------

ℤ : Type
ℤ = int ⊤ {ℕ} (λ _ → ★) ★ (λ _ → ★) ★

ℤcase : (P : ℤ → Type)
  (fneg : (n : ℕ) → P (neg n)) (fzero : P zero) (fpos : (n : ℕ) → P (pos n))
  (z : ℤ) → P z
ℤcase P = int-case {⊤} {ℕ} {λ _ → ★} {★} {λ _ → ★} {★} (λ _ → P)

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
-- Identity types
------------------------------

postulate
  ＝int : (Ω : Type) {N : Type} (ν : N → Ω) (ζ : Ω) (ψ : N → Ω)
    (ω : Ω) (u v : int Ω ν ζ ψ ω) →
    (u ＝ v) ≡
    int (＝Idx Ω (int Ω ν ζ ψ)) {IDty N}
        (＝toIdx Ω (int Ω ν ζ ψ) ν neg)
        (ζ , ζ , refl ζ , zero , zero)
        (＝toIdx Ω (int Ω ν ζ ψ) ψ pos)
        (ω , ω , refl ω , u , v)
  Id-int : {Δ : Tel} (Ω : el Δ → Type) {N : el Δ → Type}
    (ν : (x : el Δ) → N x → Ω x) (ζ : (x : el Δ) → Ω x) (ψ : (x : el Δ) → N x → Ω x)
    (ω : (x : el Δ) → Ω x) (δ : el (ID Δ))
    (u₀ : int (Ω (δ ₀)) (ν (δ ₀)) (ζ (δ ₀)) (ψ (δ ₀)) (ω (δ ₀)))
    (u₁ : int (Ω (δ ₁)) (ν (δ ₁)) (ζ (δ ₁)) (ψ (δ ₁)) (ω (δ ₁))) →
    Id (Λ x ⇨ int (Ω x) (ν x) (ζ x) (ψ x) (ω x)) δ u₀ u₁ ≡
    int (Id-Idx δ Ω (λ x y → int (Ω x) (ν x) (ζ x) (ψ x) y)) {IDty′ N δ}
         (Id-toIdx δ Ω (λ x y → int (Ω x) (ν x) (ζ x) (ψ x) y) ν (λ x n → neg n))
         (ζ (δ ₀) , ζ (δ ₁) , ap (Λ⇨ Ω) ζ δ , zero , zero)
         (Id-toIdx δ Ω (λ x y → int (Ω x) (ν x) (ζ x) (ψ x) y) ψ (λ x n → pos n))
         (ω (δ ₀) , ω (δ ₁) , ap (Λ⇨ Ω) ω δ , u₀ , u₁)

{-# REWRITE ＝int Id-int #-}

------------------------------
-- Arithmetic
------------------------------

ℤsuc : ℤ → ℤ
ℤsuc = ℤcase _ (ind _ zero (λ n' _ → (neg n'))) (pos Z) (λ n → pos (S n))

ℤpred : ℤ → ℤ
ℤpred = ℤcase _ (λ n → neg (S n)) (neg Z) (ind _ zero (λ n' _ → (pos n')))

ℤsuc-pred : (z : ℤ) → ℤsuc (ℤpred z) ＝ z
ℤsuc-pred = ℤcase _ (λ n → refl (neg n)) (refl zero) (ind _ (refl (pos Z)) (λ n' pf → refl (pos (S n'))))

ℤpred-suc : (z : ℤ) → ℤpred (ℤsuc z) ＝ z
ℤpred-suc = ℤcase _  (ind _ (refl (neg Z)) (λ n' pf → refl (neg (S n')))) (refl zero) (λ n → refl (pos n))
