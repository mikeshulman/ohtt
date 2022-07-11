{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Int.Base where

import Agda.Builtin.Nat
import Agda.Builtin.Int

open import HOTT.Rewrite using (Type; _≡_)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Unit
open import HOTT.Sigma.Base
open import HOTT.Nat
open import HOTT.Indices
open import HOTT.Groupoids

infix 40 _+ℤ_ _*ℤ_
infix 35 _＝ℤ_

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

data ℤ : Type where
--ℤ = int ⊤ {ℕ} (λ _ → ★) ★ (λ _ → ★) ★
  neg : ℕ → ℤ
  zero : ℤ
  pos : ℕ → ℤ

ℤcase : (P : ℤ → Type)
  (fneg : (n : ℕ) → P (neg n)) (fzero : P zero) (fpos : (n : ℕ) → P (pos n))
  (z : ℤ) → P z
-- int-case {⊤} {ℕ} {λ _ → ★} {★} {λ _ → ★} {★} (λ _ → P)
ℤcase P fneg fzero fpos (neg n) = fneg n
ℤcase P fneg fzero fpos zero = fzero
ℤcase P fneg fzero fpos (pos n) = fpos n

ι : ℕ → ℤ
ι Z = zero
ι (S n) = pos n

−ι : ℕ → ℤ
−ι Z = zero
−ι (S n) = neg n

----------------------------------------
-- Identity types of ordinary integers
----------------------------------------

data _＝ℤ_ : ℤ → ℤ → Type where
  neg : {x y : ℕ} → (x ＝ y) → neg x ＝ℤ neg y
  zero : zero ＝ℤ zero
  pos : {x y : ℕ} → (x ＝ y) → pos x ＝ℤ pos y

＝ℤcase : (P : (x y : ℤ) → (x ＝ℤ y) → Type)
  (fneg : (m n : ℕ) (e : m ＝ n) → P (neg m) (neg n) (neg e))
  (fzero : P zero zero zero)
  (fpos : (m n : ℕ) (e : m ＝ n) → P (pos m) (pos n) (pos e))
  {x y : ℤ} (e : x ＝ℤ y) → P x y e
＝ℤcase P fneg fzero fpos {(neg m)} {(neg n)} (neg e) = fneg m n e
＝ℤcase P fneg fzero fpos {.zero} {.zero} zero = fzero
＝ℤcase P fneg fzero fpos {(pos m)} {(pos n)} (pos e) = fpos m n e

cong-ι : {m n : ℕ} (e : m ＝ℕ n) → ι m ＝ℤ ι n
cong-ι Z = zero
cong-ι (S e) = pos e

------------------------------
-- Special path operations
------------------------------

-- Unfortunately, with Z and S being constructors of more than one
-- datatype, Agda can't guess what something like (refl Z) means.  So
-- we define separate operations just for natural numbers.

reflℤ : (n : ℤ) → (n ＝ n)
reflℤ n = refl n

revℤ : {m n : ℤ} → (m ＝ n) → (n ＝ m)
revℤ p = rev {ℤ} p

_•ℤ_ : {x y z : ℤ} → (x ＝ y) → (y ＝ z) → x ＝ z
p •ℤ q = _•_ {ℤ} p q

refl＝ℤ : {m n : ℤ} (p : m ＝ n) → (p ＝ p)
refl＝ℤ p = refl p

rev＝ℤ : {m n : ℤ} {p q : m ＝ n} → (p ＝ q) → (q ＝ p)
rev＝ℤ {m} {n} r = rev {m ＝ n} r

_•＝ℤ_ : {m n : ℤ} {x y z : m ＝ n} → (x ＝ y) → (y ＝ z) → x ＝ z
_•＝ℤ_ {m} {n} p q = _•_ {m ＝ n} p q

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
  ＝-ℤ : (x y : ℤ) → (x ＝ y) ≡ (x ＝ℤ y)

{-# REWRITE ＝int Id-int ＝-ℤ #-}

postulate
  ＝-＝ℤ : (n₀ n₁ : ℤ) (e₀ e₁ : n₀ ＝ℤ n₁) →
    (e₀ ＝ e₁) ≡
    int (Σ[ x₀ ⦂ ℤ ] Σ[ x₁ ⦂ ℤ ] (x₀ ＝ x₁) × (x₀ ＝ x₁))
      {Σ[ x₀ ⦂ ℕ ] Σ[ x₁ ⦂ ℕ ] (x₀ ＝ x₁) × (x₀ ＝ x₁)}
      (λ m → (neg (fst m) , neg (fst (snd m)) ,
              neg (fst (snd (snd m))) , neg (snd (snd (snd m)))))
      (zero , zero , zero , zero)
      (λ m → (pos (fst m) , pos (fst (snd m)) ,
              pos (fst (snd (snd m))) , pos (snd (snd (snd m)))))
      (n₀ , n₁ , e₀ , e₁)
  Id-＝ℤ : {Δ : Tel} (δ : el (ID Δ)) (n₀ n₁ : el Δ → ℤ)
    (e₀ : n₀ (δ ₀) ＝ℤ n₁ (δ ₀)) (e₁ : n₀ (δ ₁) ＝ℤ n₁ (δ ₁)) →
    Id {Δ} (Λ x ⇨ n₀ x ＝ℤ n₁ x) δ e₀ e₁ ≡
    int (Σ[ x₀₀ ⦂ ℤ ] Σ[ x₀₁ ⦂ ℤ ] Σ[ x₀₂ ⦂ x₀₀ ＝ x₀₁ ]
         Σ[ x₁₀ ⦂ ℤ ] Σ[ x₁₁ ⦂ ℤ ] Σ[ x₁₂ ⦂ x₁₀ ＝ x₁₁ ]
         (x₀₀ ＝ℤ x₁₀) × (x₀₁ ＝ℤ x₁₁))
      {Σ[ x₀₀ ⦂ ℕ ] Σ[ x₀₁ ⦂ ℕ ] Σ[ x₀₂ ⦂ x₀₀ ＝ x₀₁ ]
       Σ[ x₁₀ ⦂ ℕ ] Σ[ x₁₁ ⦂ ℕ ] Σ[ x₁₂ ⦂ x₁₀ ＝ x₁₁ ]
       (x₀₀ ＝ℕ x₁₀) × (x₀₁ ＝ℕ x₁₁)}
      (λ m → neg (fst m) , neg (fst (snd m)) , neg (fst (snd (snd m))) ,
             neg (fst (snd (snd (snd m)))) , neg (fst (snd (snd (snd (snd m))))) ,
             neg (fst (snd (snd (snd (snd (snd m)))))) ,
             neg (fst (snd (snd (snd (snd (snd (snd m))))))) ,
             neg (snd (snd (snd (snd (snd (snd (snd m))))))))
      (zero , zero , zero , zero , zero , zero , zero , zero)
      (λ m → pos (fst m) , pos (fst (snd m)) , pos (fst (snd (snd m))) ,
             pos (fst (snd (snd (snd m)))) , pos (fst (snd (snd (snd (snd m))))) ,
             pos (fst (snd (snd (snd (snd (snd m)))))) ,
             pos (fst (snd (snd (snd (snd (snd (snd m))))))) ,
             pos (snd (snd (snd (snd (snd (snd (snd m))))))))
      (n₀ (δ ₀) , n₀ (δ ₁) , ap (Λ _ ⇨ ℤ) n₀ δ ,
       n₁ (δ ₀) , n₁ (δ ₁) , ap (Λ _ ⇨ ℤ) n₁ δ ,
       e₀ , e₁)

{-# REWRITE ＝-＝ℤ Id-＝ℤ #-}

------------------------------
-- Arithmetic
------------------------------

ℤsuc : ℤ → ℤ
ℤsuc = ℤcase _ (ind _ zero (λ n' _ → (neg n'))) (pos Z) (λ n → pos (S n))

ℤpred : ℤ → ℤ
ℤpred = ℤcase _ (λ n → neg (S n)) (neg Z) (ind _ zero (λ n' _ → (pos n')))

ℤsuc-pred : (z : ℤ) → ℤsuc (ℤpred z) ＝ z
ℤsuc-pred = ℤcase _ (λ n → reflℤ (neg n)) (reflℤ zero) (ind _ (reflℤ (pos Z)) (λ n' pf → reflℤ (pos (S n'))))

ℤpred-suc : (z : ℤ) → ℤpred (ℤsuc z) ＝ z
ℤpred-suc = ℤcase _  (ind _ (reflℤ (neg Z)) (λ n' pf → reflℤ (neg (S n')))) (reflℤ zero) (λ n → reflℤ (pos n))

_−ℕ_ : ℕ → ℕ → ℤ
_−ℕ_ = ind _ (ind _ zero (λ n _ → neg n)) (λ m m- → ind _ (pos m) λ n _ → m- n)

_+ℤ_ : ℤ → ℤ → ℤ
_+ℤ_ = ℤcase _
  (λ m → ℤcase _ (λ n → neg (S (m +ℕ n))) (neg m) (λ n → n −ℕ m))
  (λ n → n)
  (λ m → ℤcase _ (λ n → m −ℕ n) (pos m) (λ n → pos (S (m +ℕ n))))

_*ℤ_ : ℤ → ℤ → ℤ
_*ℤ_ = ℤcase _
  (λ m → ℤcase _ (λ n → ι (S m *ℕ S n)) zero λ n → −ι (S m *ℕ S n))
  (λ _ → zero)
  (λ m → ℤcase _ (λ n → −ι (S m *ℕ S n)) zero λ n → ι (S m *ℕ S n))
