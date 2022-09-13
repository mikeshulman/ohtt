{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Square.Simple where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe.Parametric
open import HOTT.Functoriality

--------------------
-- Squares
--------------------

-- We introduce a two-dimensional mixfix syntax, using box-drawing
-- symbols, for specifying the boundary of a square.  Hopefully the
-- examples below should make clear how to use it.  When working with
-- this syntax, you may find Emacs's "rectangle" commands helpful.
-- Unfortunately, Agda can't be told to *display* this syntax with
-- appropriate newlines and indentation (I believe Coq could), so it
-- only looks nice in the source code.

record ∂2 (A : Type) (a₀₀ a₀₁ a₁₀ a₁₁ : A) : Typeᵉ where
  constructor ┌─_─┐_□_└─_─┘
  infix 70 _₀₂ _₁₂ _₂₀ _₂₁

  field
    _₁₂ : a₁₀ ＝ a₁₁
    _₂₀ : a₀₀ ＝ a₁₀
    _₂₁ : a₀₁ ＝ a₁₁
    _₀₂ : a₀₀ ＝ a₀₁
open ∂2 public

Sq : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁) → Type
Sq A {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  Id {A × A} (λ u → fst u ＝ snd u) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a ₀₂ , a ₁₂) (a ₂₀) (a ₂₁)

--------------------
-- Symmetry
--------------------

postulate
  sym : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁) →
    Sq A ┌─   a ₁₂    ─┐
         a ₂₀   □   a ₂₁
         └─   a ₀₂    ─┘  →  Sq A ┌─   a ₂₁    ─┐
                                  a ₀₂   □   a ₁₂
                                  └─   a ₂₀    ─┘

sym-∂2 : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → ∂2 A a₀₀ a₀₁ a₁₀ a₁₁ → ∂2 A a₀₀ a₁₀ a₀₁ a₁₁
sym-∂2 ┌─  a₁₂  ─┐
      a₂₀  □  a₂₁
      └─  a₀₂  ─┘ = ┌─  a₂₁  ─┐
                    a₀₂  □  a₁₂
                    └─  a₂₀  ─┘

postulate
  sym-sym : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁) →
    (a₂₂ : Sq A ┌─   a ₁₂    ─┐
                a ₂₀   □   a ₂₁
                └─   a ₀₂    ─┘) → sym A (sym-∂2 a) (sym A a a₂₂) ≡ a₂₂
{-# REWRITE sym-sym #-}

refl-∂2 : {A : Type} (a : A) → ∂2 A a a a a
refl-∂2 a = ┌─     refl a     ─┐
           refl a   □    refl a
           └─     refl a     ─┘

-- Like Id-refl and ap-refl, this should be admissible in concrete
-- cases like Σ and Π, but probably must fire explicitly when A is a
-- variable type, or when A is a type like the universe or maybe even
-- any type without an η-rule like a (co)inductive one.  I also don't
-- know how to deal with the case when A is variable or η-free but a
-- is an eliminator, since then (refl a) is volatile and could appear
-- in a reduced form, preventing firing of the rewrite.  It would work
-- if sym reduces on its term argument instead of its type; maybe we
-- could deal with the Π-case of that by *also* inspecting the type
-- when we see that the term is a ƛ?
postulate
  sym-refl-refl : (A : Type) (a : A) → sym A (refl-∂2 a) (refl (refl a)) ≡ refl (refl a)
{-# REWRITE sym-refl-refl #-}

postulate
  ap-refl-sym : {Δ : Type} (A : Type) (f : Δ → A) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap {Δ} {λ x → f x ＝ f x} (λ x → refl (f x)) δ₂ ≡
    sym A ┌─  refl (f δ₁)  ─┐
          ap f δ₂  □  ap f δ₂
          └─  refl (f δ₀)  ─┘  (refl (ap f δ₂))
{-# REWRITE ap-refl-sym #-}

