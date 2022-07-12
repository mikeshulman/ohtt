{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Empty where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Indices
open import HOTT.Sigma.Base
open import HOTT.Pi.Base
open import HOTT.Groupoids

data empty (Ω : Type) : Ω → Type where

empty-elim : {Ω : Type} (P : (x : Ω) → empty Ω x → Type)
  {ω : Ω} (e : empty Ω ω) → P ω e
empty-elim P ()

data ⊥ : Type where

⊥-elim : (P : ⊥ → Type) (e : ⊥) → P e
⊥-elim P ()

postulate
  ＝⊥ : (u v : ⊥) → (u ＝ v) ≡ empty (⊥ × ⊥) (u , v)
  ＝-empty : (Ω : Type) (ω : Ω) (u v : empty Ω ω) →
    (u ＝ v) ≡ empty (＝Idx Ω (empty Ω)) (ω , ω , refl ω , u , v)
  Id-empty : {Δ : Tel} (Ω : el Δ → Type) (ω : (x : el Δ) → Ω x) (δ : el (ID Δ))
    (u₀ : empty (Ω (δ ₀)) (ω (δ ₀))) (u₁ : empty (Ω (δ ₁)) (ω (δ ₁))) →
    Id (Λ x ⇨ empty (Ω x) (ω x)) δ u₀ u₁ ≡
    empty (Id-Idx δ Ω (λ x y → empty (Ω x) y)) (ω (δ ₀) , ω (δ ₁) , ap (Λ⇨ Ω) ω δ , u₀ , u₁)

{-# REWRITE ＝⊥ ＝-empty Id-empty #-}

isProp-⊥ : isProp ⊥
isProp-⊥ = ƛ x ⇒ ⊥-elim (λ x → Π[ y ⦂ ⊥ ] x ＝ y) x
