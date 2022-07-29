{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Rewrite where

open import Agda.Primitive renaming (Set to Type; SSet to Typeᵉ) public

infix 10 _≡_ _≡ᵉ_
infixr 35 _•ᶠ_ _•ᵉ_ _•ʰ_

------------------------------
-- Strict equality
------------------------------

-- Because we don't assume cumulativity, we have two strict
-- equalities, one for elements of types and one for elements of
-- exotypes.  We decorate operations involving the first with ᶠ (for
-- fibrant) and the second with ᵉ.  The exception is the equality type
-- itself, where we write ≡ instead of ≡ᶠ.

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

revᶠ : {A : Type} {a b : A} (p : a ≡ b) → b ≡ a
revᶠ reflᵉ = reflᵉ

revᵉ : {A : Typeᵉ} {a b : A} (p : a ≡ᵉ b) → b ≡ᵉ a
revᵉ reflᵉᵉ = reflᵉᵉ

-- Congruence operations are annotated by their input sort(s) and output sort.

congᶠᶠ : {A : Type} {B : Type} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
congᶠᶠ f reflᵉ = reflᵉ

congᵉᶠ : {A : Typeᵉ} {B : Type} (f : A → B) {x y : A} (p : x ≡ᵉ y) → f x ≡ f y
congᵉᶠ f reflᵉᵉ = reflᵉ

congᵉᵉ : {A B : Typeᵉ} (f : A → B) {x y : A} (p : x ≡ᵉ y) → f x ≡ᵉ f y
congᵉᵉ f reflᵉᵉ = reflᵉᵉ

congᶠᶠᶠ : {A B C : Type} (f : A → B → C) {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v) → f x u ≡ f y v
congᶠᶠᶠ f reflᵉ reflᵉ = reflᵉ

congᶠᶠᶠᶠ : {A B C D : Type} (f : A → B → C → D) {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v) {c d : C} (r : c ≡ d) → f x u c ≡ f y v d
congᶠᶠᶠᶠ f reflᵉ reflᵉ reflᵉ = reflᵉ

coeᶠ→ : {A B : Type} → (A ≡ B) → A → B
coeᶠ→ reflᵉ u = u

coeᶠ← : {A B : Type} → (A ≡ B) → B → A
coeᶠ← reflᵉ v = v

axiomKᶠ : {A : Type} {a : A} {p : a ≡ a} → p ≡ᵉ reflᵉ
axiomKᶠ {p = reflᵉ} = reflᵉᵉ

axiomKᵉ : {A : Typeᵉ} {a : A} {p : a ≡ᵉ a} → p ≡ᵉ reflᵉᵉ
axiomKᵉ {p = reflᵉᵉ} = reflᵉᵉ

uipᶠ : {A : Type} {a b : A} {p q : a ≡ b} → p ≡ᵉ q
uipᶠ {q = reflᵉ} = axiomKᶠ

uipᵉ : {A : Typeᵉ} {a b : A} {p q : a ≡ᵉ b} → p ≡ᵉ q
uipᵉ {q = reflᵉᵉ} = axiomKᵉ

postulate
  funextᶠ : {A : Type} {B : A → Type} {f f' : (x : A) → B x} (p : (x : A) → f x ≡ f' x) →
    f ≡ f'
  funextᶠ-refl : {A : Type} {B : A → Type} (f : (x : A) → B x) (p : (x : A) → f x ≡ f x) →
    funextᶠ p ≡ᵉ reflᵉ

{-# REWRITE funextᶠ-refl #-}

------------------------------
-- Heterogeneous equality
------------------------------

-- We restrict heterogeneous equality to elements of types, not
-- exotypes.  This suffices for our applications, and simplifies a lot
-- of reasoning about it since we don't have to coerce equalities of
-- types to equalities of their underlying exotypes or worry about
-- whether we can go the other direction.  Heterogeneous operations
-- are annotated by ʰ.

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

-- There are a lot of potential different kinds of congruence
-- involving heterogeneous equality, and I'm not sure of an
-- appropriate systematic naming scheme.  At the moment these are all
-- commented out until we find out how many of them we need in this
-- iteration of the library.

{-
congᶠʰ : {A : Type} {B : A → Type} (f : (x : A) → B x) {a a' : A} (e : a ≡ a') → f a ≡ʰ f a'
congᶠʰ f reflᵉ = reflʰ

congᶠᶠʰ : {A B : Type} {C : A → B → Type} (f : (x : A) (y : B) → C x y)
  {a a' : A} (u : a ≡ a') {b b' : B} (v : b ≡ b') → f a b ≡ʰ f a' b'
congᶠᶠʰ f reflᵉ reflᵉ = reflʰ

congdᶠʰʰ : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} (f : (x : A) (y : B x) → C x y)
  {a a' : A} (u : a ≡ a') {b : B a} {b' : B a'} (v : b ≡ʰ b') → f a b ≡ʰ f a' b'
congdᶠʰʰ f reflᵉ reflʰ = reflʰ

congʰ : {A B A' B' : Type} {f : A → B} {f' : A' → B'} (u : A ≡ A') (v : B ≡ B') (e : f ≡ʰ f')
  {x : A} {x' : A'} (p : x ≡ʰ x') → f x ≡ʰ f' x'
congʰ reflᵉ reflᵉ reflʰ reflʰ = reflʰ

congʰʰ : {A B C A' B' C' : Type} {f : A → B → C} {f' : A' → B' → C'}
  (u : A ≡ A') (v : B ≡ B') (w : C ≡ C') (e : f ≡ʰ f')
  {x : A} {x' : A'} (p : x ≡ʰ x') {y : B} {y' : B'} (q : y ≡ʰ y') → f x y ≡ʰ f' x' y'
congʰʰ reflᵉ reflᵉ reflᵉ reflʰ reflʰ reflʰ = reflʰ

congdʰʰʰ : {A : Type} {B : A → Type} {C : (x : A) → B x → Type}
          {A' : Type} {B' : A' → Type} {C' : (x : A') → B' x → Type}
          {f : (x : A) (y : B x) → C x y} {f' : (x : A') (y : B' x) → C' x y}
  (u : A ≡ A') (v : B ≡ʰ B') (w : C ≡ʰ C') (e : f ≡ʰ f')
  {x : A} {x' : A'} (p : x ≡ʰ x') {y : B x} {y' : B' x'} (q : y ≡ʰ y') → f x y ≡ʰ f' x' y'
congdʰʰʰ reflᵉ reflʰ reflʰ reflʰ reflʰ reflʰ = reflʰ
-}

≡ʰ→≡ : {A : Type} {a₀ a₁ : A} → (a₀ ≡ʰ a₁) → (a₀ ≡ a₁)
≡ʰ→≡ reflʰ = reflᵉ

axiomKʰ : {A : Type} {a : A} {p : a ≡ʰ a} → p ≡ᵉ reflʰ
axiomKʰ {p = reflʰ} = reflᵉᵉ

postulate
  funextʰ : {A : Type} {B : A → Type} {A' : Type} {B' : A' → Type}
    {f : (x : A) → B x} {f' : (x : A') → B' x} (p : (x : A) (x' : A') → (x ≡ʰ x') → f x ≡ʰ f' x') →
    f ≡ʰ f'
  funextʰ-refl : {A : Type} {B : A → Type} (f : (x : A) → B x)
    (p : (x x' : A) → (x ≡ʰ x') → f x ≡ʰ f x') →
    funextʰ p ≡ᵉ reflʰ

{-# REWRITE funextʰ-refl #-}

coeᶠ→≡ʰ : {A B : Type} (e : A ≡ B) (a : A) → coeᶠ→ e a ≡ʰ a
coeᶠ→≡ʰ reflᵉ _ = reflʰ

coeᶠ←≡ʰ : {A B : Type} (e : A ≡ B) (b : B) → coeᶠ← e b ≡ʰ b
coeᶠ←≡ʰ reflᵉ _ = reflʰ

coeᶠ←←≡ʰ : {A B C : Type} (u : A ≡ B) (v : B ≡ C) (c : C) → coeᶠ← u (coeᶠ← v c) ≡ʰ c
coeᶠ←←≡ʰ reflᵉ reflᵉ _ = reflʰ

coeᶠ→←←←≡ʰ : {A B C D E : Type} (u : A ≡ B) (v : A ≡ C) (w : C ≡ D) (x : D ≡ E) (e : E) →
  coeᶠ→ u (coeᶠ← v (coeᶠ← w (coeᶠ← x e))) ≡ʰ e
coeᶠ→←←←≡ʰ reflᵉ reflᵉ reflᵉ reflᵉ _ = reflʰ

coeᶠ→≡ʰcoeᶠ→← : {A B C D : Type} (u : A ≡ B) (v : C ≡ D) (w : C ≡ A) (a : A) →
  coeᶠ→ u a ≡ʰ (coeᶠ→ v (coeᶠ← w a))
coeᶠ→≡ʰcoeᶠ→← reflᵉ reflᵉ reflᵉ a = reflʰ
