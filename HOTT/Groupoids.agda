{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Groupoids where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Fill

infixr 35 _•_

_•_ : {A : Type} {x y z : A} (p : x ＝ y) (q : y ＝ z) → x ＝ z
_•_ {A} {x} {y} {z} p q = comp→ {ε} (Λ _ ⇨ A) [] {x} {x} (refl x) {y} {z} q p

module ＝-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _＝⟨⟩_ _＝⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A} → (x ＝ y) → (x ＝ y)
  begin p = p

  _＝⟨⟩_ : ∀ (x : A) {y : A} → (x ＝ y) → (x ＝ y)
  x ＝⟨⟩ p = p

  _＝⟨_⟩_ : ∀ (x : A) {y z : A} → (x ＝ y) → (y ＝ z) → (x ＝ z)
  x ＝⟨ p ⟩ q = p • q

  _∎ : ∀ (x : A) → (x ＝ x)
  x ∎ = refl x

open ＝-Reasoning
