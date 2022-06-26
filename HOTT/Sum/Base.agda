{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Sum.Base where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Unit
open import HOTT.Sigma.Base

data sum (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) : Ω → Type where
  inl : (a : A) → sum Ω α β (α a)
  inr : (b : B) → sum Ω α β (β b)

case : {Ω : Type} {A B : Type} {α : A → Ω} {β : B → Ω}
  (ω : Ω) (s : sum Ω α β ω)
  (C : (x : Ω) → sum Ω α β x → Type)
  (f : (a : A) → C (α a) (inl a)) (g : (b : B) → C (β b) (inr b))
  → C ω s
case _ (inl a) C f g = f a
case _ (inr b) C f g = g b

_⊎_ : Type → Type → Type
A ⊎ B = sum ⊤ {A} {B} (λ _ → ★) (λ _ → ★) ★

postulate
  ＝sum : (Ω : Type) {A B : Type} (α : A → Ω) (β : B → Ω) (ω : Ω) (u v : sum Ω α β ω) →
    (u ＝ v) ≡
    sum (Σ[ x₀ ﹕ Ω ] Σ[ x₁ ﹕ Ω ] Σ[ x₂ ﹕ x₀ ＝ x₁ ] Σ[ s₀ ﹕ sum Ω α β x₀ ] (sum Ω α β x₁))
         {Σ[ a₀ ﹕ A ] Σ[ a₁ ﹕ A ] (a₀ ＝ a₁)} {Σ[ b₀ ﹕ B ] Σ[ b₁ ﹕ B ] (b₀ ＝ b₁)}
         (λ a → α (π₁ a) ﹐ α (π₁ (π₂ a)) ﹐ ap {ε ▸ (λ _ → A)} (λ x → α (top x)) ([] ∷ π₁ a ∷ π₁ (π₂ a) ∷ π₂ (π₂ a)) ﹐
                inl (π₁ a) ﹐ inl (π₁ (π₂ a)))
         (λ b → β (π₁ b) ﹐ β (π₁ (π₂ b)) ﹐ ap {ε ▸ (λ _ → B)} (λ x → β (top x)) ([] ∷ π₁ b ∷ π₁ (π₂ b) ∷ π₂ (π₂ b)) ﹐
                inr (π₁ b) ﹐ inr (π₁ (π₂ b)))
         (ω ﹐ ω ﹐ refl ω ﹐ u ﹐ v)
  Id-sum : {Δ : Tel} (Ω : el Δ → Type) {A B : el Δ → Type}
    (α : (x : el Δ) → A x → Ω x) (β : (x : el Δ) → B x → Ω x) (ω : (x : el Δ) → Ω x)
    (δ : el (ID Δ)) (u₀ : sum (Ω (δ ₀)) (α (δ ₀)) (β (δ ₀)) (ω (δ ₀))) (u₁ : sum (Ω (δ ₁)) (α (δ ₁)) (β (δ ₁)) (ω (δ ₁))) →
    Id (λ x → sum (Ω x) (α x) (β x) (ω x)) δ u₀ u₁ ≡
    sum (Σ[ x₀ ﹕ Ω (δ ₀) ] Σ[ x₁ ﹕ Ω (δ ₁) ] Σ[ x₂ ﹕ Id Ω δ x₀ x₁ ]
          Σ[ s₀ ﹕ sum (Ω (δ ₀)) (α (δ ₀)) (β (δ ₀)) x₀ ] (sum (Ω (δ ₁)) (α (δ ₁)) (β (δ ₁)) x₁))
         {Σ[ a₀ ﹕ A (δ ₀) ] Σ[ a₁ ﹕ A (δ ₁) ] Id A δ a₀ a₁} {Σ[ b₀ ﹕ B (δ ₀) ] Σ[ b₁ ﹕ B (δ ₁) ] Id B δ b₀ b₁}
         (λ a → α (δ ₀) (π₁ a) ﹐ α (δ ₁) (π₁ (π₂ a)) ﹐
                Id-pop← Ω A δ (π₂ (π₂ a)) (ap {Δ ▸ A} (λ x → α (pop x) (top x)) (δ ∷ π₁ a ∷ π₁ (π₂ a) ∷ π₂ (π₂ a))) ﹐
                inl (π₁ a) ﹐ inl (π₁ (π₂ a)))
         (λ b → β (δ ₀) (π₁ b) ﹐ β (δ ₁) (π₁ (π₂ b)) ﹐
                Id-pop← Ω B δ (π₂ (π₂ b)) (ap {Δ ▸ B} (λ x → β (pop x) (top x)) (δ ∷ π₁ b ∷ π₁ (π₂ b) ∷ π₂ (π₂ b))) ﹐
                inr (π₁ b) ﹐ inr (π₁ (π₂ b)))
         (ω (δ ₀) ﹐ ω (δ ₁) ﹐ ap ω δ ﹐ u₀ ﹐ u₁)

{-# REWRITE ＝sum Id-sum #-}
