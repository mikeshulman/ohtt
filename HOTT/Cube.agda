module HOTT.Cube where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat

infix 50 _!₀ _!₁ _!₂ _!⁰ _!¹

----------------------------------------
-- Cubes of arbitrary dimension
----------------------------------------

CUBE : (n : ℕᵉ) (A : Type) → Type

∂ : (n : ℕᵉ) (A : Type) → Type

-- We make this a ⇒ so that its identity types are functorial automatically.
Cube : (n : ℕᵉ) (A : Type) → ∂ n A ⇒ Type

CUBE n A = Σ (∂ n A) (Cube n A ∙_)

∂ 𝐳 A = ⊤
∂ (𝐬 n) A = （ a₀ ⦂ ∂ n A ）× （ a₁ ⦂ ∂ n A ）× (a₀ ＝ a₁) × (Cube n A ∙ a₀) × (Cube n A ∙ a₁)

-- We give special names to the projections from this Σ-type.  I
-- believe that by defining these directly by pattern-matching they
-- end up as much smaller terms, in contrast to how a chain of fst-snd
-- would be annotated at each step by a large type family.  This makes
-- for a big speedup, although unfortunately ap needs separate rules
-- for computing on any definition made by pattern-matching.

_!₀ : {n : ℕᵉ} {A : Type} → ∂ (𝐬 n) A → ∂ n A
(a₀ , a₁ , a₂ , b₀ , b₁) !₀ = a₀

_!₁ : {n : ℕᵉ} {A : Type} → ∂ (𝐬 n) A → ∂ n A
(a₀ , a₁ , a₂ , b₀ , b₁) !₁ = a₁

_!₂ : {n : ℕᵉ} {A : Type} (u : ∂ (𝐬 n) A) → (u !₀ ＝ u !₁)
(a₀ , a₁ , a₂ , b₀ , b₁) !₂ = a₂

_!⁰ : {n : ℕᵉ} {A : Type} (u : ∂ (𝐬 n) A) → Cube n A ∙ u !₀
(a₀ , a₁ , a₂ , b₀ , b₁) !⁰ = b₀

_!¹ : {n : ℕᵉ} {A : Type} (u : ∂ (𝐬 n) A) → Cube n A ∙ u !₁
(a₀ , a₁ , a₂ , b₀ , b₁) !¹ = b₁

Cube 𝐳 A = ƛ _ ⇒ A
Cube (𝐬 n) A = ƛ a ⇒ Id (Cube n A ∙_) {a !₀} {a !₁} (a !₂) (a !⁰) (a !¹)
