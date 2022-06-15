{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Rewrite where

open import Agda.Primitive renaming (Set to Type; SSet to Typeᵉ) public

------------------------------
-- Strict equality
------------------------------

data _≡_ {A : Typeᵉ} (a : A) : A → Typeᵉ where
  reflᵉ : a ≡ a

infix 5 _≡_

infixr 30 _•_ _•ʰ_

{-# BUILTIN REWRITE _≡_ #-}

_•_ : {A : Typeᵉ} {a b c : A} (p : a ≡ b) (q : b ≡ c) → a ≡ c
reflᵉ • reflᵉ = reflᵉ

rev : {A : Typeᵉ} {a b : A} (p : a ≡ b) → b ≡ a
rev reflᵉ = reflᵉ

cong : {A B : Typeᵉ} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
cong f reflᵉ = reflᵉ

cong2 : {A B C : Typeᵉ} (f : A → B → C) {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v) → f x u ≡ f y v
cong2 f reflᵉ reflᵉ = reflᵉ

cong3 : {A B C D : Typeᵉ} (f : A → B → C → D) {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v) {c d : C} (r : c ≡ d) → f x u c ≡ f y v d
cong3 f reflᵉ reflᵉ reflᵉ = reflᵉ

≡Type→≡ᵉ : {A B : Type} (e : A ≡ B) → _≡_ {Typeᵉ} A B
≡Type→≡ᵉ reflᵉ = reflᵉ

-- {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) (u : B x) → B y
coe→ : {A B : Type} → (A ≡ B) → A → B
coe→ reflᵉ u = u

-- {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) (v : B y) → B x
coe← : {A B : Type} → (A ≡ B) → B → A
coe← reflᵉ v = v

-- Apparently we can't make A B : Typeᵉ in coe→, even with cumulativity
coe→ᵉ : {A B : Typeᵉ} → (A ≡ B) → A → B
coe→ᵉ reflᵉ u = u

coe←ᵉ : {A B : Typeᵉ} → (A ≡ B) → B → A
coe←ᵉ reflᵉ v = v

coe←≡ : {A : Type} {e : A ≡ A} {a : A} → coe← e a ≡ a
coe←≡ {e = reflᵉ} = reflᵉ

axiomK : {A : Typeᵉ} {a : A} {p : a ≡ a} → p ≡ reflᵉ
axiomK {p = reflᵉ} = reflᵉ

uip : {A : Typeᵉ} {a b : A} {p q : a ≡ b} → p ≡ q
uip {q = reflᵉ} = axiomK

coe←coe← : {A B C : Type} (p : A ≡ B) (q : B ≡ C) (r : A ≡ C) {c : C} → coe← p (coe← q c) ≡ coe← r c
coe←coe← reflᵉ reflᵉ reflᵉ = reflᵉ

coe→coe→ : {A B C : Type} (p : A ≡ B) (q : B ≡ C) (r : A ≡ C) {a : A} → coe→ q (coe→ p a) ≡ coe→ r a
coe→coe→ reflᵉ reflᵉ reflᵉ = reflᵉ

coe←coe←ᵉ : {A B C : Typeᵉ} (p : A ≡ B) (q : B ≡ C) (r : A ≡ C) {c : C} → coe←ᵉ p (coe←ᵉ q c) ≡ coe←ᵉ r c
coe←coe←ᵉ reflᵉ reflᵉ reflᵉ = reflᵉ

coe→coe→ᵉ : {A B C : Typeᵉ} (p : A ≡ B) (q : B ≡ C) (r : A ≡ C) {a : A} → coe→ᵉ q (coe→ᵉ p a) ≡ coe→ᵉ r a
coe→coe→ᵉ reflᵉ reflᵉ reflᵉ = reflᵉ

coe←coe→ : {A B : Type} (p : A ≡ B) {a : A} → coe← p (coe→ p a) ≡ a
coe←coe→ reflᵉ = reflᵉ

coe→coe← : {A B : Type} (p : A ≡ B) {b : B} → coe→ p (coe← p b) ≡ b
coe→coe← reflᵉ = reflᵉ

coe←coe→ᵉ : {A B : Typeᵉ} (p : A ≡ B) {a : A} → coe←ᵉ p (coe→ᵉ p a) ≡ a
coe←coe→ᵉ reflᵉ = reflᵉ

coe→coe←ᵉ : {A B : Typeᵉ} (p : A ≡ B) {b : B} → coe→ᵉ p (coe←ᵉ p b) ≡ b
coe→coe←ᵉ reflᵉ = reflᵉ

coe←coe→′ : {A B : Type} (p q : A ≡ B) (a : A) → coe← p (coe→ q a) ≡ coe← (p • rev q) a
coe←coe→′ reflᵉ reflᵉ a = reflᵉ

coe→coe←′ : {A B : Type} (p q : A ≡ B) (b : B) → coe→ p (coe← q b) ≡ coe→ (rev p • q) b
coe→coe←′ reflᵉ reflᵉ b = reflᵉ

coe←coe→ᵉ′ : {A B : Typeᵉ} (p q : A ≡ B) (a : A) → coe←ᵉ p (coe→ᵉ q a) ≡ coe←ᵉ (p • rev q) a
coe←coe→ᵉ′ reflᵉ reflᵉ a = reflᵉ

coe→coe←ᵉ′ : {A B : Typeᵉ} (p q : A ≡ B) (b : B) → coe→ᵉ p (coe←ᵉ q b) ≡ coe→ᵉ (rev p • q) b
coe→coe←ᵉ′ reflᵉ reflᵉ b = reflᵉ

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

axiomKʰ : {A : Type} {a : A} {p : a ≡ʰ a} → p ≡ reflʰ
axiomKʰ {p = reflʰ} = reflᵉ

postulate
  funextʰ : {A : Type} {B : A → Type} {A' : Type} {B' : A' → Type}
    {f : (x : A) → B x} {f' : (x : A') → B' x} (p : (x : A) (x' : A') → (x ≡ʰ x') → f x ≡ʰ f' x') →
    f ≡ʰ f'
  funextʰ-reflʰ : {A : Type} {B : A → Type} (f : (x : A) → B x)
    (p : (x x' : A) → (x ≡ʰ x') → f x ≡ʰ f x') →
    funextʰ p ≡ reflʰ

{-# REWRITE funextʰ-reflʰ #-}

coe→≡ʰ : {A B : Type} (e : A ≡ B) (a : A) → coe→ e a ≡ʰ a
coe→≡ʰ reflᵉ _ = reflʰ

coe←≡ʰ : {A B : Type} (e : A ≡ B) (b : B) → coe← e b ≡ʰ b
coe←≡ʰ reflᵉ _ = reflʰ

coe→←←←≡ʰ : {A B C D E : Type} (u : A ≡ B) (v : A ≡ C) (w : C ≡ D) (x : D ≡ E) (e : E) →
  coe→ u (coe← v (coe← w (coe← x e))) ≡ʰ e
coe→←←←≡ʰ reflᵉ reflᵉ reflᵉ reflᵉ _ = reflʰ

coe→≡ʰcoe→← : {A B C D : Type} (u : A ≡ B) (v : C ≡ D) (w : C ≡ A) (a : A) →
  coe→ u a ≡ʰ (coe→ v (coe← w a))
coe→≡ʰcoe→← reflᵉ reflᵉ reflᵉ a = reflʰ
