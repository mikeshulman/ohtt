{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Indices where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Unit
open import HOTT.Sigma.Base

------------------------------
-- Index types and indices
------------------------------

＝Idx : (Ω : Type) (S : Ω → Type) → Type
＝Idx Ω S = Σ[ x₀ ﹕ Ω ] Σ[ x₁ ﹕ Ω ] Σ[ x₂ ﹕ x₀ ＝ x₁ ] Σ[ s₀ ﹕ S x₀ ] S x₁

Id-Idx : {Δ : Tel} (δ : el (ID Δ)) (Ω : el Δ → Type)
  (S : (x : el Δ) → Ω x → Type) → Type
Id-Idx {Δ} δ Ω S =
  Σ[ x₀ ﹕ Ω (δ ₀) ] Σ[ x₁ ﹕ Ω (δ ₁) ] Σ[ x₂ ﹕ Id (Λ⇨ Ω) δ x₀ x₁ ]
  Σ[ s₀ ﹕ S (δ ₀) x₀ ] S (δ ₁) x₁

IDty : (A : Type) → Type
IDty A = Σ[ a₀ ﹕ A ] Σ[ a₁ ﹕ A ] (a₀ ＝ a₁)

IDty′ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) → Type
IDty′ {Δ} A δ = Σ[ a₀ ﹕ A (δ ₀) ] Σ[ a₁ ﹕ A (δ ₁) ] Id (Λ⇨ A) δ a₀ a₁

＝toIdx : (Ω : Type) (S : Ω → Type) {A : Type} (α : A → Ω) (i : (a : A) → S (α a)) →
  IDty A → ＝Idx Ω S
＝toIdx Ω S {A} α i (a₀ , a₁ , a₂) =
  (α a₀ , α a₁ ,
  ap {ε▸ A} ((Λ _ ⇨ Ω) ⊚ POP) (λ x → α (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂),
  i a₀ , i a₁)

Id-toIdx : {Δ : Tel} (δ : el (ID Δ)) (Ω : el Δ → Type) (S : (x : el Δ) → Ω x → Type)
  {A : el Δ → Type} (α : (x : el Δ) → A x → Ω x) (i : (x : el Δ) → (a : A x) → S x (α x a)) →
  IDty′ A δ → Id-Idx δ Ω S
Id-toIdx {Δ} δ Ω S {A} α i (a₀ , a₁ , a₂) =
  (α (δ ₀) a₀ , α (δ ₁) a₁ ,
   ap {Δ ▸ Λ⇨ A} ((Λ⇨ Ω) ⊚ POP) (λ x → α (pop x) (top x)) (δ ∷ a₀ ∷ a₁ ∷ a₂) ,
   i (δ ₀) a₀ , i (δ ₁) a₁)

----------------------------------------
-- Equality of indices and index types
----------------------------------------

ΣΣ≡Σ : (A₀ A₁ : Type) {A₂ A₂' : A₀ → A₁ → Type} (p : A₂ ≡ A₂') (B : A₀ → A₁ → Type) →
  (Σ[ x₀ ﹕ A₀ ] Σ[ x₁ ﹕ A₁ ] Σ[ x₂ ﹕ A₂ x₀ x₁ ] B x₀ x₁)
  ≡ Σ[ x₀ ﹕ A₀ ] Σ[ x₁ ﹕ A₁ ] Σ[ x₂ ﹕ A₂' x₀ x₁ ] B x₀ x₁
ΣΣ≡Σ A₀ A₁ reflᵉ B = reflᵉ

,,≡ʰ, : {A₀ A₁ : Type} {A₂ A₂' : A₀ → A₁ → Type} (p : A₂ ≡ A₂') {B : A₀ → A₁ → Type}
  (a₀ : A₀) (a₁ : A₁) {a₂ : A₂ a₀ a₁} {a₂' : A₂' a₀ a₁} (q : a₂ ≡ʰ a₂') (b : B a₀ a₁) →
  _≡ʰ_
  {Σ[ x₀ ﹕ A₀ ] Σ[ x₁ ﹕ A₁ ] Σ[ x₂ ﹕ A₂ x₀ x₁ ] B x₀ x₁}
  (a₀ , a₁ , a₂ , b)
  {Σ[ x₀ ﹕ A₀ ] Σ[ x₁ ﹕ A₁ ] Σ[ x₂ ﹕ A₂' x₀ x₁ ] B x₀ x₁}
  (a₀ , a₁ , a₂' , b)
,,≡ʰ, reflᵉ a₀ a₁ reflʰ b = reflʰ

ΣΣ≡ : (A₀ A₁ : Type) {A₂ A₂' : A₀ → A₁ → Type} (p : A₂ ≡ A₂') →
  (Σ[ x₀ ﹕ A₀ ] Σ[ x₁ ﹕ A₁ ] A₂ x₀ x₁)
  ≡ Σ[ x₀ ﹕ A₀ ] Σ[ x₁ ﹕ A₁ ] A₂' x₀ x₁
ΣΣ≡ A₀ A₁ reflᵉ = reflᵉ

IDty′-pop : {Δ : Tel} (C : Δ ⇨ Type) (A : el Δ → Type) (δ : el (ID Δ))
  (c₀ : C ⊘ (δ ₀)) (c₁ : C ⊘ (δ ₁)) (c₂ : Id C δ c₀ c₁) →
  IDty′ A δ ≡ IDty′ (λ z → A (pop {B = C} z)) (δ ∷ c₀ ∷ c₁ ∷ c₂)
IDty′-pop {Δ} C A δ c₀ c₁ c₂ =
  ΣΣ≡ (A (δ ₀)) (A (δ ₁))
     (funextᵉ (λ x₀ → funextᵉ λ x₁ → rev (Id-AP (λ x → pop {B = C} x) (δ ∷ c₀ ∷ c₁ ∷ c₂) (Λ⇨ A) x₀ x₁)))
