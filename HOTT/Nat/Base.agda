{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Nat.Base where

import Agda.Builtin.Nat

open import HOTT.Rewrite using (Type; _≡_)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Unit
open import HOTT.Empty
open import HOTT.Sum.Base
open import HOTT.Pi.Base
open import HOTT.Sigma.Base
open import HOTT.Indices
open import HOTT.Groupoids
open import HOTT.Decidable

infix 40 _+ℕ_ _*ℕ_
infix 35 _＝ℕ_

----------------------------------------
-- Generalized Natural numbers
----------------------------------------

data nat (Ω : Type) (ζ : Ω) (σ : Ω → Ω) : Ω → Type where
  Z : nat Ω ζ σ ζ
  S : {x : Ω} → nat Ω ζ σ x → nat Ω ζ σ (σ x)
open nat

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

-- We could define ℕ as 
--- ℕ = nat ⊤ ★ (λ _ → ★) ★
-- but then it would get expanded everywhere, producing
-- hard-to-understand goals.  So we define it as a separate datatype.
data ℕ : Type where
  Z : ℕ
  S : ℕ → ℕ
open ℕ

ind : (P : ℕ → Type) (z : P Z) (f : (n : ℕ) → P n → P (S n)) →
  (n : ℕ) → P n
--ind P z f n = nat-ind {⊤} {★} {λ _ → ★} {★} (λ _ → P) z (λ _ → f) n
ind P z f Z = z
ind P z f (S n) = f n (ind P z f n)

----------------------------------------
-- Equality of ordinary naturals
----------------------------------------

-- Similarly, we could define the identity types of ℕ in terms of the
-- general nat, but again that would produce hard-to-understand goals.
-- So we make it a separate (indexed) datatype as well.
data _＝ℕ_ : ℕ → ℕ → Type where
  Z : Z ＝ℕ Z
  S : {m n : ℕ} → (m ＝ℕ n) → (S m ＝ℕ S n)

＝ind : (P : (m n : ℕ) → (m ＝ℕ n) → Type) (z : P Z Z Z)
  (f : (m n : ℕ) (e : m ＝ℕ n) → P m n e → P (S m) (S n) (S e)) →
  {m n : ℕ} (e : m ＝ℕ n) → P m n e
＝ind P z f Z = z
＝ind P z f (S e) = f _ _ _ (＝ind P z f e)

-- However, after these two stages we stop doing things by hand: the
-- identity types of ＝ℕ are an instance of nat.

------------------------------
-- Special path operations
------------------------------

-- Unfortunately, with Z and S being constructors of more than one
-- datatype, Agda can't guess what something like (refl Z) means.  So
-- we define separate operations just for natural numbers.

reflℕ : (n : ℕ) → (n ＝ n)
reflℕ n = refl n

revℕ : {m n : ℕ} → (m ＝ n) → (n ＝ m)
revℕ p = rev {ℕ} p

_⊙ℕ_ : {x y z : ℕ} → (x ＝ y) → (y ＝ z) → x ＝ z
p ⊙ℕ q = _⊙_ {ℕ} p q

refl＝ℕ : {m n : ℕ} (p : m ＝ n) → (p ＝ p)
refl＝ℕ p = refl p

rev＝ℕ : {m n : ℕ} {p q : m ＝ n} → (p ＝ q) → (q ＝ p)
rev＝ℕ {m} {n} r = rev {m ＝ n} r

_⊙＝ℕ_ : {m n : ℕ} {x y z : m ＝ n} → (x ＝ y) → (y ＝ z) → x ＝ z
_⊙＝ℕ_ {m} {n} p q = _⊙_ {m ＝ n} p q

----------------------------------------
-- Pretty input and output
----------------------------------------

record Number (A : Type) : Type where
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
            ap {Δ ▸ Λ⇨ Ω} (Λ⇨ Ω ⊚ POP) (λ x → σ (pop x) (top x))
               (δ ∷ fst m ∷ fst (snd m) ∷ fst (snd (snd m))) ,
            S (fst (snd (snd (snd m)))) , S (snd (snd (snd (snd m)))))
         (ω (δ ₀) , ω (δ ₁) , ap (Λ⇨ Ω) ω δ , n₀ , n₁)
  ＝nat :  (Ω : Type) (ζ : Ω) (σ : Ω → Ω) (ω : Ω)
           (n₀ n₁ : nat Ω ζ σ ω) →
    (n₀ ＝ n₁) ≡
    nat (＝Idx Ω (λ y → nat Ω ζ σ y))
        (ζ , ζ , refl ζ , Z , Z)
        (λ m →
           σ (fst m) , σ (fst (snd m)) ,
           ap {ε▸ Ω} (Λ _ ⇨ Ω) (λ x → σ (top x))
              ([] ∷ fst m ∷ fst (snd m) ∷ fst (snd (snd m))) ,
           S (fst (snd (snd (snd m)))) , S (snd (snd (snd (snd m)))))
         (ω , ω , refl ω , n₀ , n₁)
  ＝-ℕ : (n₀ n₁ : ℕ) →
    (n₀ ＝ n₁) ≡ (n₀ ＝ℕ n₁)
  -- We don't need an Id-ℕ since ℕ is constant, so Id ℕ automatically
  -- reduces to ＝.

{-# REWRITE Id-nat ＝nat ＝-ℕ #-}

postulate
  ＝-＝ℕ : (n₀ n₁ : ℕ) (e₀ e₁ : n₀ ＝ℕ n₁) →
    (e₀ ＝ e₁) ≡
    nat (Σ[ x₀ ⦂ ℕ ] Σ[ x₁ ⦂ ℕ ] (x₀ ＝ x₁) × (x₀ ＝ x₁))
      (Z , Z , Z , Z)
      (λ m → (S (fst m) , S (fst (snd m)) ,
              S (fst (snd (snd m))) , S (snd (snd (snd m)))))
      (n₀ , n₁ , e₀ , e₁)
  Id-＝ℕ : {Δ : Tel} (δ : el (ID Δ)) (n₀ n₁ : el Δ → ℕ)
    (e₀ : n₀ (δ ₀) ＝ℕ n₁ (δ ₀)) (e₁ : n₀ (δ ₁) ＝ℕ n₁ (δ ₁)) →
    Id {Δ} (Λ x ⇨ n₀ x ＝ℕ n₁ x) δ e₀ e₁ ≡
    nat (Σ[ x₀₀ ⦂ ℕ ] Σ[ x₀₁ ⦂ ℕ ] Σ[ x₀₂ ⦂ x₀₀ ＝ x₀₁ ]
          Σ[ x₁₀ ⦂ ℕ ] Σ[ x₁₁ ⦂ ℕ ] Σ[ x₁₂ ⦂ x₁₀ ＝ x₁₁ ]
          (x₀₀ ＝ℕ x₁₀) × (x₀₁ ＝ℕ x₁₁))
      (Z , Z , Z , Z , Z , Z , Z , Z)
      (λ m → S (fst m) , S (fst (snd m)) , S (fst (snd (snd m))) ,
             S (fst (snd (snd (snd m)))) , S (fst (snd (snd (snd (snd m))))) ,
             S (fst (snd (snd (snd (snd (snd m)))))) ,
             S (fst (snd (snd (snd (snd (snd (snd m))))))) ,
             S (snd (snd (snd (snd (snd (snd (snd m))))))))
      (n₀ (δ ₀) , n₀ (δ ₁) , ap (Λ _ ⇨ ℕ) n₀ δ ,
       n₁ (δ ₀) , n₁ (δ ₁) , ap (Λ _ ⇨ ℕ) n₁ δ ,
       e₀ , e₁)

{-# REWRITE ＝-＝ℕ Id-＝ℕ #-}

----------------------------------------
-- Decidable equality and sethood
----------------------------------------

ℕcode : ℕ → ℕ → Type
ℕcode = ind _ (ind _ ⊤ (λ _ _ → ⊥)) (λ m m＝ → ind _ ⊥ (λ n _ → m＝ n))

ℕencode : {m n : ℕ} → (m ＝ℕ n) → ℕcode m n
ℕencode e = ＝ind (λ m n _ → ℕcode m n) ★ (λ _ _ _ p → p) e

ℕdecode : {m n : ℕ} → (ℕcode m n) → (m ＝ℕ n)
ℕdecode {m} {n} =
  ind (λ m → (n : ℕ) → (ℕcode m n) → (m ＝ℕ n))
    (λ n → ind (λ n → (ℕcode Z n) → (Z ＝ℕ n))
      (λ _ → Z) (λ _ _ e → ⊥-elim (λ _ → Z ＝ℕ S _) e) n)
    (λ m' m'≟ n → (ind (λ n → (ℕcode (S m') n) → (S m' ＝ℕ n))
      (⊥-elim (λ _ → S m' ＝ℕ Z))
      (λ n' Sm'≟n' e → S (m'≟ n' e))
      n))
    m n

Z≠S : (n : ℕ) → (Z ＝ℕ S n) ⇒ ⊥
Z≠S n = ƛ e ⇒ ℕencode e

S≠Z : (n : ℕ) → (S n ＝ℕ Z) ⇒ ⊥
S≠Z n = ƛ e ⇒ ℕencode e

Sinj : {m n : ℕ} → (S m ＝ℕ S n) → (m ＝ℕ n)
Sinj e = ℕdecode (ℕencode e)

deceq-ℕ : DecEq ℕ
deceq-ℕ = ƛ m ⇒ ƛ n ⇒
  ind (λ m → (n : ℕ) → (m ＝ n) ⊎ (m ＝ n ⇒ ⊥))
    (λ n → ind (λ n → (Z ＝ n) ⊎ (Z ＝ n ⇒ ⊥)) (inl Z) (λ _ _ → inr (Z≠S _)) n)
    (λ m' m'≟ n → ind (λ n → (S m' ＝ n) ⊎ (S m' ＝ n ⇒ ⊥)) (inr (S≠Z _))
      (λ n' Sm'≟n' → case (m'≟ n') _ (λ e → inl (S e)) λ e → inr (ƛ ne ⇒ e ∙ (Sinj ne)))
      n)
    m n

isSet-ℕ : isSet ℕ
isSet-ℕ = hedberg deceq-ℕ

------------------------------
-- Arithmetic
------------------------------

_+ℕ_ : ℕ → ℕ → ℕ
_+ℕ_ = ind _ (λ n → n) (λ m m+ n → S (m+ n))

+ℕ0 : (x : ℕ) → x +ℕ 0 ＝ x
+ℕ0 = ind _ (refl {ℕ} Z) (λ x +ℕ0x → S +ℕ0x)

+ℕassoc : (x y z : ℕ) → (x +ℕ y) +ℕ z ＝ x +ℕ (y +ℕ z)
+ℕassoc = ind _ (λ y z → refl (y +ℕ z)) (λ x xassoc y z → S (xassoc y z))

+ℕS : (x y : ℕ) → (x +ℕ S y ＝ S (x +ℕ y))
+ℕS = ind _ (λ y → reflℕ (S y)) (λ x IH y → S (IH y))

+ℕcomm : (x y : ℕ) → (x +ℕ y ＝ y +ℕ x)
+ℕcomm = ind _ (λ y → revℕ (+ℕ0 y))
  (λ x IH y →
  begin
    S (x +ℕ y)
  ＝⟨ S (IH y) ⟩
    S (y +ℕ x)
  ＝⟨ revℕ (+ℕS y x) ⟩
    (y +ℕ S x)
  ∎)

_*ℕ_ : ℕ → ℕ → ℕ
_*ℕ_ = ind _ (λ _ → Z) (λ m m* n → n +ℕ (m* n))
