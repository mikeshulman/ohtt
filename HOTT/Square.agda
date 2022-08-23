{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Square where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe

--------------------
-- Squares
--------------------

record ∂ (A : Type) (a₀₀ a₀₁ a₁₀ a₁₁ : A) : Type where
  constructor ┌─_─┐_□_└─_─┘
  infix 70 _₀₂ _₁₂ _₂₀ _₂₁

  field
    _₁₂ : a₁₀ ＝ a₁₁
    _₂₀ : a₀₀ ＝ a₁₀
    _₂₁ : a₀₁ ＝ a₁₁
    _₀₂ : a₀₀ ＝ a₀₁
open ∂

Sq : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁) → Type
Sq A {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  Id {A × A} (λ u → fst u ＝ snd u) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a ₀₂ , a ₁₂) (a ₂₀) (a ₂₁)

--------------------
-- Symmetry
--------------------

sym-∂ : {A : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} → ∂ A a₀₀ a₀₁ a₁₀ a₁₁ → ∂ A a₀₀ a₁₀ a₀₁ a₁₁
sym-∂ ┌─  a₁₂  ─┐
      a₂₀  □  a₂₁
      └─  a₀₂  ─┘ = ┌─  a₂₁  ─┐
                    a₀₂  □  a₁₂
                    └─  a₂₀  ─┘

refl-∂ : {A : Type} (a : A) → ∂ A a a a a
refl-∂ a = ┌─     refl a     ─┐
           refl a   □    refl a
           └─     refl a     ─┘

postulate
  sym : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁) →
    Sq A ┌─   a ₁₂    ─┐
         a ₂₀   □   a ₂₁
         └─   a ₀₂    ─┘  →  Sq A ┌─   a ₂₁    ─┐
                                  a ₀₂   □   a ₁₂
                                  └─   a ₂₀    ─┘
  sym-sym : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁) →
    (a₂₂ : Sq A ┌─   a ₁₂    ─┐
                a ₂₀   □   a ₂₁
                └─   a ₀₂    ─┘) → sym A (sym-∂ a) (sym A a a₂₂) ≡ a₂₂
  -- This relies on Id-refl, for well-typedness
  sym-refl-refl : (A : Type) (a : A) → sym A (refl-∂ a) (refl (refl a)) ≡ refl (refl a)
{-# REWRITE sym-sym sym-refl-refl #-}

------------------------------
-- Composition and filling
------------------------------

record ┬ : Type where
  constructor ⁇

-- We don't wrap composition and square-filling into ⇒ types, so we
-- name them with → and ← instead of ⇒ and ⇐.

comp→ : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) → a₀₁ ＝ a₁₁
comp→ A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  tr⇒ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₀

comp_┌─_─┐_⇛_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (_ : ┬) (a₀₂ : a₀₀ ＝ a₀₁) → a₀₁ ＝ a₁₁
comp A ┌─  a₁₂  ─┐
       a₂₀  ⇛    ⁇
       └─  a₀₂  ─┘ = comp→ A a₀₂ a₁₂ a₂₀

fill→ : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) →
  Sq A ┌─  a₁₂  ─┐
       a₂₀  □  comp→ A a₀₂ a₁₂ a₂₀
       └─  a₀₂  ─┘
fill→ A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift⇒ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₀

fill_┌─_─┐_⇛_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (_ : ┬) (a₀₂ : a₀₀ ＝ a₀₁) →
  Sq A ┌─  a₁₂         ─┐
       a₂₀  □  comp→ A a₀₂ a₁₂ a₂₀
       └─  a₀₂         ─┘
fill A ┌─  a₁₂  ─┐
       a₂₀  ⇛    ⁇
       └─  a₀₂  ─┘ = fill→ A a₀₂ a₁₂ a₂₀

comp← : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₁ : a₀₁ ＝ a₁₁) → a₀₀ ＝ a₁₀
comp← A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr⇐ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₁

comp_┌─_─┐_⇚_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (_ : ┬) (a₂₁ : a₀₁ ＝ a₁₁) (a₀₂ : a₀₀ ＝ a₀₁) → a₀₀ ＝ a₁₀
comp A ┌─  a₁₂  ─┐
       ⁇    ⇚  a₂₁
       └─  a₀₂  ─┘ = comp← A a₀₂ a₁₂ a₂₁

fill← : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A         ┌─          a₁₂   ─┐
       comp← A a₀₂ a₁₂ a₂₁  □   a₂₁
               └─          a₀₂   ─┘
fill← A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift⇐ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₁

fill_┌─_─┐_⇚_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (_ : ┬) (a₂₁ : a₀₁ ＝ a₁₁) (a₀₂ : a₀₀ ＝ a₀₁) →
  Sq A ┌─                  a₁₂   ─┐
       comp← A a₀₂ a₁₂ a₂₁  □   a₂₁
       └─                  a₀₂   ─┘
fill A ┌─  a₁₂  ─┐
       ⁇    ⇚  a₂₁
       └─  a₀₂  ─┘ = fill← A a₀₂ a₁₂ a₂₁

comp↑ : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) → a₁₀ ＝ a₁₁
comp↑ A a₀₂ a₂₀ a₂₁ = comp→ A a₂₀ a₂₁ a₀₂

comp_┌─_─┐_⤊_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (_ : ┬) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) (a₀₂ : a₀₀ ＝ a₀₁) → a₁₀ ＝ a₁₁
comp A ┌─   ⁇   ─┐
       a₂₀  ⤊  a₂₁
       └─  a₀₂  ─┘ = comp↑ A a₀₂ a₂₀ a₂₁

fill↑ : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A ┌─  comp↑ A a₀₂ a₂₀ a₂₁  ─┐
       a₂₀          □          a₂₁
       └─          a₀₂          ─┘
fill↑ A a₀₂ a₂₀ a₂₁ = sym A ┌─  a₂₁                     ─┐
                            a₀₂  □    comp→ A a₂₀ a₂₁ a₀₂
                            └─  a₂₀                     ─┘   fill A ┌─  a₂₁  ─┐
                                                                    a₀₂  ⇛    ⁇
                                                                    └─  a₂₀  ─┘

fill_┌─_─┐_⤊_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (_ : ┬) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) (a₀₂ : a₀₀ ＝ a₀₁) →
  Sq A ┌─  comp↑ A a₀₂ a₂₀ a₂₁  ─┐
       a₂₀          □          a₂₁
       └─          a₀₂          ─┘
fill A ┌─   ⁇   ─┐
       a₂₀  ⤊  a₂₁
       └─  a₀₂  ─┘ = fill↑ A a₀₂ a₂₀ a₂₁

comp↓ : (A : Type) {a₀₀ a₀₁ : A} {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) → a₀₀ ＝ a₀₁
comp↓ A a₁₂ a₂₀ a₂₁ = comp← A a₂₀ a₂₁ a₁₂

comp_┌─_─┐_⤋_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) (_ : ┬) → a₀₀ ＝ a₀₁
comp A ┌─  a₁₂  ─┐
       a₂₀  ⤋  a₂₁
       └─   ⁇   ─┘ = comp↓ A a₁₂ a₂₀ a₂₁

fill↓ : (A : Type) {a₀₀ a₀₁ : A} {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A ┌─          a₁₂          ─┐
       a₂₀          □          a₂₁
       └─  comp↓ A a₁₂ a₂₀ a₂₁  ─┘
fill↓ A a₁₂ a₂₀ a₂₁ = sym A ┌─                  a₂₁  ─┐
                            comp← A a₂₀ a₂₁ a₁₂  □  a₁₂
                            └─                  a₂₀  ─┘   fill A ┌─  a₂₁  ─┐
                                                                 ⁇    ⇚  a₁₂
                                                                 └─  a₂₀  ─┘

fill_┌─_─┐_⤋_└─_─┘ : (A : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) (_ : ┬) →
  Sq A ┌─          a₁₂          ─┐
       a₂₀          □          a₂₁
       └─  comp↓ A a₁₂ a₂₀ a₂₁  ─┘
fill A ┌─  a₁₂  ─┐
       a₂₀  ⤋  a₂₁
       └─   ⁇   ─┘ = fill↓ A a₁₂ a₂₀ a₂₁

------------------------------
-- Dependent squares
------------------------------

record ∂ᵈ {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁) (a₂₂ : Sq A a)
  (b₀₀ : B ∙ a₀₀) (b₀₁ : B ∙ a₀₁) (b₁₀ : B ∙ a₁₀) (b₁₁ : B ∙ a₁₁) : Type where
  constructor ╔═_═╗_□_╚═_═╝
  infix 70 _₁₂ _₂₀ _₂₁ _₀₂
  field
    _₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁
    _₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀
    _₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁
    _₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁
open ∂ᵈ

Sqᵈ : {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂ A a₀₀ a₀₁ a₁₀ a₁₁)
      (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                  a ₂₀   □    a ₂₁
                  └─    a ₀₂    ─┘)
      {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁} (b : ∂ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) → Type
Sqᵈ {A} B {a₀₀} {a₀₁} {a₁₀} {a₁₁} a a₂₂ {b₀₀} {b₀₁} {b₁₀} {b₁₁} b =
  Id {（ a₀ ⦂ A ）× （ a₁ ⦂ A ）× （ a₂ ⦂ a₀ ＝ a₁ ）× B ∙ a₀ × B ∙ a₁}
      (λ u → Id (B ∙_) (₃rd u) (₄th u) (₅th' u))
      {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀}
      {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁}
      (a ₀₂ , a ₁₂ , a₂₂ , b ₀₂ , b ₁₂)
      (b ₂₀)
      (b ₂₁)

------------------------------
-- TODO: Dependent symmetry
------------------------------



------------------------------------------------------------
-- TODO: Dependent square-filling
------------------------------------------------------------
