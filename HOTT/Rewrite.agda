{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Rewrite where

open import Agda.Primitive renaming (Set to Type; SSet to Typeᵉ) public

infix 10 _≡_ _≡ᵉ_
infixr 35 _•ᶠ_ _•ʰ_

------------------------------
-- Strict equality
------------------------------

data _≡_ {A : Type} (a : A) : A → Typeᵉ where
  reflᵉ : a ≡ a

data _≡ᵉ_ {A : Typeᵉ} (a : A) : A → Typeᵉ where
  reflᵉᵉ : a ≡ᵉ a

{-# BUILTIN REWRITE _≡_ #-}
{-# BUILTIN REWRITE _≡ᵉ_ #-}

_•ᶠ_ : {A : Type} {a b c : A} (p : a ≡ b) (q : b ≡ c) → a ≡ c
reflᵉ •ᶠ reflᵉ = reflᵉ

_•ᵉ_ : {A : Typeᵉ} {a b c : A} (p : a ≡ᵉ b) (q : b ≡ᵉ c) → a ≡ᵉ c
reflᵉᵉ •ᵉ reflᵉᵉ = reflᵉᵉ

rev : {A : Type} {a b : A} (p : a ≡ b) → b ≡ a
rev reflᵉ = reflᵉ

revᵉ : {A : Typeᵉ} {a b : A} (p : a ≡ᵉ b) → b ≡ᵉ a
revᵉ reflᵉᵉ = reflᵉᵉ

congᶠ : {A : Type} {B : Type} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
congᶠ f reflᵉ = reflᵉ

cong : {A : Typeᵉ} {B : Type} (f : A → B) {x y : A} (p : x ≡ᵉ y) → f x ≡ f y
cong f reflᵉᵉ = reflᵉ

congᵉ : {A B : Typeᵉ} (f : A → B) {x y : A} (p : x ≡ᵉ y) → f x ≡ᵉ f y
congᵉ f reflᵉᵉ = reflᵉᵉ

cong2 : {A B C : Type} (f : A → B → C) {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v) → f x u ≡ f y v
cong2 f reflᵉ reflᵉ = reflᵉ

cong3 : {A B C D : Type} (f : A → B → C → D) {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v) {c d : C} (r : c ≡ d) → f x u c ≡ f y v d
cong3 f reflᵉ reflᵉ reflᵉ = reflᵉ

coe→ : {A B : Type} → (A ≡ B) → A → B
coe→ reflᵉ u = u

coe← : {A B : Type} → (A ≡ B) → B → A
coe← reflᵉ v = v

axiomK : {A : Type} {a : A} {p : a ≡ a} → p ≡ᵉ reflᵉ
axiomK {p = reflᵉ} = reflᵉᵉ

axiomKᵉ : {A : Typeᵉ} {a : A} {p : a ≡ᵉ a} → p ≡ᵉ reflᵉᵉ
axiomKᵉ {p = reflᵉᵉ} = reflᵉᵉ

uip : {A : Type} {a b : A} {p q : a ≡ b} → p ≡ᵉ q
uip {q = reflᵉ} = axiomK

------------------------------
-- Heterogeneous equality
------------------------------

-- We restrict heterogeneous equality to elements of types, not
-- exotypes.  This suffices for our applications, and simplifies a lot
-- of reasoning about it since we don't have to coerce equalities of
-- types to equalities of their underlying exotypes or worry about
-- whether we can go the other direction.

data _≡ʰ_ {A : Type} (a : A) : {B : Type} → B → Typeᵉ where
  reflʰ : a ≡ʰ a

≡→≡ʰ : {A : Type} {a b : A} → a ≡ b → a ≡ʰ b
≡→≡ʰ reflᵉ = reflʰ

_•ʰ_ : {A B C : Type} {a : A} {b : B} {c : C} (e : a ≡ʰ b) (f : b ≡ʰ c) → a ≡ʰ c
reflʰ •ʰ reflʰ = reflʰ

revʰ : {A B : Type} {a : A} {b : B} → (a ≡ʰ b) → (b ≡ʰ a)
revʰ reflʰ = reflʰ

≡ʰ→≡Type : {A B : Type} {a : A} {b : B} (e : a ≡ʰ b) → A ≡ B
≡ʰ→≡Type reflʰ = reflᵉ

scongʰ : {A : Type} {B : A → Type} (f : (x : A) → B x) {a a' : A} (e : a ≡ a') → f a ≡ʰ f a'
scongʰ f reflᵉ = reflʰ

scong2ʰ : {A B : Type} {C : A → B → Type} (f : (x : A) (y : B) → C x y)
  {a a' : A} (u : a ≡ a') {b b' : B} (v : b ≡ b') → f a b ≡ʰ f a' b'
scong2ʰ f reflᵉ reflᵉ = reflʰ

scong2dʰ : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} (f : (x : A) (y : B x) → C x y)
  {a a' : A} (u : a ≡ a') {b : B a} {b' : B a'} (v : b ≡ʰ b') → f a b ≡ʰ f a' b'
scong2dʰ f reflᵉ reflʰ = reflʰ

congʰ : {A B A' B' : Type} {f : A → B} {f' : A' → B'} (u : A ≡ A') (v : B ≡ B') (e : f ≡ʰ f')
  {x : A} {x' : A'} (p : x ≡ʰ x') → f x ≡ʰ f' x'
congʰ reflᵉ reflᵉ reflʰ reflʰ = reflʰ

cong2ʰ : {A B C A' B' C' : Type} {f : A → B → C} {f' : A' → B' → C'}
  (u : A ≡ A') (v : B ≡ B') (w : C ≡ C') (e : f ≡ʰ f')
  {x : A} {x' : A'} (p : x ≡ʰ x') {y : B} {y' : B'} (q : y ≡ʰ y') → f x y ≡ʰ f' x' y'
cong2ʰ reflᵉ reflᵉ reflᵉ reflʰ reflʰ reflʰ = reflʰ

cong2dʰ : {A : Type} {B : A → Type} {C : (x : A) → B x → Type}
          {A' : Type} {B' : A' → Type} {C' : (x : A') → B' x → Type}
          {f : (x : A) (y : B x) → C x y} {f' : (x : A') (y : B' x) → C' x y}
  (u : A ≡ A') (v : B ≡ʰ B') (w : C ≡ʰ C') (e : f ≡ʰ f')
  {x : A} {x' : A'} (p : x ≡ʰ x') {y : B x} {y' : B' x'} (q : y ≡ʰ y') → f x y ≡ʰ f' x' y'
cong2dʰ reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ = reflʰ

≡ʰ→≡ : {A : Type} {a₀ a₁ : A} → (a₀ ≡ʰ a₁) → (a₀ ≡ a₁)
≡ʰ→≡ reflʰ = reflᵉ

axiomKʰ : {A : Type} {a : A} {p : a ≡ʰ a} → p ≡ᵉ reflʰ
axiomKʰ {p = reflʰ} = reflᵉᵉ

postulate
  funextʰ : {A : Type} {B : A → Type} {A' : Type} {B' : A' → Type}
    {f : (x : A) → B x} {f' : (x : A') → B' x} (p : (x : A) (x' : A') → (x ≡ʰ x') → f x ≡ʰ f' x') →
    f ≡ʰ f'
  funextʰ-reflʰ : {A : Type} {B : A → Type} (f : (x : A) → B x)
    (p : (x x' : A) → (x ≡ʰ x') → f x ≡ʰ f x') →
    funextʰ p ≡ᵉ reflʰ

{-# REWRITE funextʰ-reflʰ #-}

coe→≡ʰ : {A B : Type} (e : A ≡ B) (a : A) → coe→ e a ≡ʰ a
coe→≡ʰ reflᵉ _ = reflʰ

coe←≡ʰ : {A B : Type} (e : A ≡ B) (b : B) → coe← e b ≡ʰ b
coe←≡ʰ reflᵉ _ = reflʰ

coe←←≡ʰ : {A B C : Type} (u : A ≡ B) (v : B ≡ C) (c : C) → coe← u (coe← v c) ≡ʰ c
coe←←≡ʰ reflᵉ reflᵉ _ = reflʰ

coe→←←←≡ʰ : {A B C D E : Type} (u : A ≡ B) (v : A ≡ C) (w : C ≡ D) (x : D ≡ E) (e : E) →
  coe→ u (coe← v (coe← w (coe← x e))) ≡ʰ e
coe→←←←≡ʰ reflᵉ reflᵉ reflᵉ reflᵉ _ = reflʰ

coe→≡ʰcoe→← : {A B C D : Type} (u : A ≡ B) (v : C ≡ D) (w : C ≡ A) (a : A) →
  coe→ u a ≡ʰ (coe→ v (coe← w a))
coe→≡ʰcoe→← reflᵉ reflᵉ reflᵉ a = reflʰ
