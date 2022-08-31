{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Cube where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat

infix 31 _⸴_⸴_⸴_⸴_

------------------------------
-- Quinary Σ-types
------------------------------

data Σ⁵ (A B : Type) (C : A → B → Type) (D : A → Type) (E : B → Type) : Type where
  _⸴_⸴_⸴_⸴_ : (a : A) (b : B) (c : C a b) (d : D a) (e : E b) → Σ⁵ A B C D E
open Σ⁵

module _ {A B : Type} {C : A → B → Type} {D : A → Type} {E : B → Type} where

  infix 50 _!₀ _!₁ _!₂ _!⁰ _!¹

  _!₀ : Σ⁵ A B C D E → A
  (a ⸴ b ⸴ c ⸴ d ⸴ e) !₀ = a

  _!₁ : Σ⁵ A B C D E → B
  (a ⸴ b ⸴ c ⸴ d ⸴ e) !₁ = b

  _!₂ : (u : Σ⁵ A B C D E) → C (u !₀) (u !₁)
  (a ⸴ b ⸴ c ⸴ d ⸴ e) !₂ = c

  _!⁰ : (u : Σ⁵ A B C D E) → D (u !₀)
  (a ⸴ b ⸴ c ⸴ d ⸴ e) !⁰ = d

  _!¹ : (u : Σ⁵ A B C D E) → E (u !₁)
  (a ⸴ b ⸴ c ⸴ d ⸴ e) !¹ = e

  postulate
    ηΣ⁵ : (u : Σ⁵ A B C D E) → (u !₀ ⸴ u !₁ ⸴ u !₂ ⸴ u !⁰ ⸴ u !¹) ≡ u
    ηΣ⁵-β : (a : A) (b : B) (c : C a b) (d : D a) (e : E b) →
      ηΣ⁵ (a ⸴ b ⸴ c ⸴ d ⸴ e) ≡ᵉ reflᵉ
  {-# REWRITE ηΣ⁵-β #-}

----------------------------------------
-- Identifications in Σ⁵-types
----------------------------------------

postulate
  ＝-Σ⁵ : {A B : Type} {C : A → B → Type} {D : A → Type} {E : B → Type}
    (u v : Σ⁵ A B C D E) → (u ＝ v) ≡
    Σ⁵ (u !₀ ＝ v !₀) (u !₁ ＝ v !₁)
       (λ w₀ w₁ → Id (uncurry C) {u !₀ , u !₁} {v !₀ , v !₁} (w₀ , w₁) (u !₂) (v !₂))
       (λ w₀ → Id D w₀ (u !⁰) (v !⁰)) (λ w₁ → Id E w₁ (u !¹) (v !¹))
{-# REWRITE ＝-Σ⁵ #-}

-- We postpone the rest to later.

----------------------------------------
-- Cubes of arbitrary dimension
----------------------------------------

CUBE : (n : ℕᵉ) (A : Type) → Type

∂ : (n : ℕᵉ) (A : Type) → Type

-- We make this a ⇒ so that its identity types are functorial automatically.
Cube : (n : ℕᵉ) (A : Type) → ∂ n A ⇒ Type

CUBE n A = Σ (∂ n A) (Cube n A ∙_)

∂ 𝐳 A = ⊤
∂ (𝐬 n) A = Σ⁵ (∂ n A) (∂ n A) (_＝_ {∂ n A}) (Cube n A ∙_) (Cube n A ∙_)

Cube 𝐳 A = ƛ _ ⇒ A
Cube (𝐬 n) A = ƛ a ⇒ Id (Cube n A ∙_) {a !₀} {a !₁} (a !₂) (a !⁰) (a !¹)
