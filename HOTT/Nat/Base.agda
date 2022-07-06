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
open import HOTT.Indices

infix 40 _+ℕ_ _*ℕ_

----------------------------------------
-- Generalized Natural numbers
----------------------------------------

data nat (Ω : Type) (ζ : Ω) (σ : Ω → Ω) : Ω → Type where
  Z : nat Ω ζ σ ζ
  S : {x : Ω} → nat Ω ζ σ x → nat Ω ζ σ (σ x)

nat-ind : {Ω : Type} {ζ : Ω} {σ : Ω → Ω} {ω : Ω}
  (C : (x : Ω) → nat Ω ζ σ x → Type)
  (fzero : C ζ Z)
  (fsuc : (x : Ω) (n : nat Ω ζ σ x) → C x n → C (σ x) (S n))
  (n : nat Ω ζ σ ω) →
  C ω n
nat-ind C fzero fsuc Z = fzero
nat-ind C fzero fsuc (S n) = fsuc _ _ (nat-ind C fzero fsuc n)

------------------------------
-- Ordinary natural numbers
------------------------------

ℕ : Type
ℕ = nat ⊤ ★ (λ _ → ★) ★

ind : (P : ℕ → Type) (z : P Z) (f : (n : ℕ) → P n → P (S n)) →
  (n : ℕ) → P n
ind P z f n = nat-ind {⊤} {★} {λ _ → ★} {★} (λ _ → P) z (λ _ → f) n

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
-- Identity types
------------------------------

postulate
  Id-nat : {Δ : Tel} (δ : el (ID Δ))
           (Ω : (x : el Δ) → Type) (ζ : (x : el Δ) → Ω x)
           (σ : (x : el Δ) → Ω x → Ω x) (ω : (x : el Δ) → Ω x)
           (n₀ : nat (Ω (δ ₀)) (ζ (δ ₀)) (σ (δ ₀)) (ω (δ ₀)))
           (n₁ : nat (Ω (δ ₁)) (ζ (δ ₁)) (σ (δ ₁)) (ω (δ ₁))) →
    Id (Λ x ⇨ nat (Ω x) (ζ x) (σ x) (ω x)) δ n₀ n₁ ≡
    nat (Id-Idx δ Ω (λ x y → nat (Ω x) (ζ x) (σ x) y))
         (ζ (δ ₀) , ζ (δ ₁) , ap (Λ⇨ Ω) ζ δ , Z , Z)
         (λ m →
            σ (δ ₀) (fst m) , σ (δ ₁) (fst (snd m)) ,
            ap {Δ ▸ Λ⇨ Ω} (Λ⇨ Ω ⊚ POP) (λ x → σ (pop x) (top x)) (δ ∷ fst m ∷ fst (snd m) ∷ fst (snd (snd m))) ,
            S (fst (snd (snd (snd m)))) , S (snd (snd (snd (snd m)))))
         (ω (δ ₀) , ω (δ ₁) , ap (Λ⇨ Ω) ω δ , n₀ , n₁)
  ＝nat :  (Ω : Type) (ζ : Ω) (σ : Ω → Ω) (ω : Ω)
           (n₀ n₁ : nat Ω ζ σ ω) →
    (n₀ ＝ n₁) ≡
    nat (＝Idx Ω (λ y → nat Ω ζ σ y))
        (ζ , ζ , refl ζ , Z , Z)
        (λ m →
           σ (fst m) , σ (fst (snd m)) ,
           ap {ε▸ Ω} (Λ _ ⇨ Ω) (λ x → σ (top x)) ([] ∷ fst m ∷ fst (snd m) ∷ fst (snd (snd m))) ,
           S (fst (snd (snd (snd m)))) , S (snd (snd (snd (snd m)))))
         (ω , ω , refl ω , n₀ , n₁)

{-# REWRITE Id-nat ＝nat #-}

------------------------------
-- Arithmetic
------------------------------

_+ℕ_ : ℕ → ℕ → ℕ
m +ℕ n = ind _ n (λ m m+n → S (m+n)) m

_*ℕ_ : ℕ → ℕ → ℕ
m *ℕ n = ind _ Z (λ m m*n → n +ℕ m*n) m

-- We prove (x +ℕ 0 ＝ x) in two ways, by congruence applied to S, and
-- using the fact that ＝ℕ computes.

+ℕ0 : (x : ℕ) → x +ℕ 0 ＝ x
+ℕ0 Z = refl Z
+ℕ0 (S x) = refl (ƛ n ⇒ S n) ∙ (x +ℕ 0) ∙ x ∙ (+ℕ0 x)

+ℕ0′ : (x : ℕ) → x +ℕ 0 ＝ x
+ℕ0′ Z = refl Z
+ℕ0′ (S x) = S (+ℕ0′ x)
