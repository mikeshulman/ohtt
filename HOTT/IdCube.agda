module HOTT.IdCube where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe.Parametric
open import HOTT.Functoriality
open import HOTT.Square.Simple
open import HOTT.Unit

------------------------------
-- Computing ap on !s
------------------------------

-- Recall that the projections such as _!₀ were defined by
-- pattern-matching for speed reasons, which mandates special
-- definitions for ap.  Here we give those definitions for ap,
-- reducing all the ap-!s to ‼s that are also defined by
-- pattern-matching.  To be completely correct, we'd also need to then
-- define ap on the ‼s, perhaps at that point reducing them to fst-snd
-- chains so that the standard rules for ap can take over, but in
-- practice I hope that is never necessary.

-- Unfortunately, the ‼s seem to require too many explicit arguments
-- to be written postfix like the !s.
‼₀ : {n : ℕᵉ} {A : Type} (u₀ u₁ : ∂ (𝐬 n) A) → (u₀ ＝ u₁) → (u₀ !₀ ＝ u₁ !₀)
‼₀ (a₀₀ , a₁₀ , a₂₀ , b₀₀ , b₁₀) (a₀₁ , a₁₁ , a₂₁ , b₀₁ , b₁₁) (a₀₂ , a₁₂ , a₂₂ , b₀₂ , b₁₂) = a₀₂

‼₁ : {n : ℕᵉ} {A : Type} (u₀ u₁ : ∂ (𝐬 n) A) → (u₀ ＝ u₁) → (u₀ !₁ ＝ u₁ !₁)
‼₁ (a₀₀ , a₁₀ , a₂₀ , b₀₀ , b₁₀) (a₀₁ , a₁₁ , a₂₁ , b₀₁ , b₁₁) (a₀₂ , a₁₂ , a₂₂ , b₀₂ , b₁₂) = a₁₂

postulate
  ap-!₀ : {n : ℕᵉ} {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 n) A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → u δ !₀) δ₂ ≡ ‼₀ (u δ₀) (u δ₁) (ap u δ₂)
  ap-!₁ : {n : ℕᵉ} {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 n) A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → u δ !₁) δ₂ ≡ ‼₁ (u δ₀) (u δ₁) (ap u δ₂)
  refl-!₀ : {n : ℕᵉ} {A : Type} (u : ∂ (𝐬 n) A) →
    refl (u !₀) ≡ ‼₀ u u (refl u)
  refl-!₁ : {n : ℕᵉ} {A : Type} (u : ∂ (𝐬 n) A) →
    refl (u !₁) ≡ ‼₁ u u (refl u)
{-# REWRITE ap-!₀ ap-!₁ refl-!₀ refl-!₁ #-}

‼₂ : {n : ℕᵉ} {A : Type} (u₀ u₁ : ∂ (𝐬 n) A) (u₂ : u₀ ＝ u₁) →
  Id {∂ n A × ∂ n A} (λ x → fst x ＝ snd x)
    {u₀ !₀ , u₀ !₁} {u₁ !₀ , u₁ !₁}
    (‼₀ u₀ u₁ u₂ , ‼₁ u₀ u₁ u₂)
    (u₀ !₂) (u₁ !₂)
‼₂ (a₀₀ , a₁₀ , a₂₀ , b₀₀ , b₁₀) (a₀₁ , a₁₁ , a₂₁ , b₀₁ , b₁₁) (a₀₂ , a₁₂ , a₂₂ , b₀₂ , b₁₂) = a₂₂

postulate
  ap-!₂ : {n : ℕᵉ} {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 n) A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → u δ !₂) δ₂ ≡ ‼₂ (u δ₀) (u δ₁) (ap u δ₂)
  refl-!₂ : {n : ℕᵉ} {A : Type} (u : ∂ (𝐬 n) A) →
    refl (u !₂) ≡ ‼₂ u u (refl u)
{-# REWRITE ap-!₂ refl-!₂ #-}

‼⁰ : {n : ℕᵉ} {A : Type} (u₀ u₁ : ∂ (𝐬 n) A) (u₂ : u₀ ＝ u₁) →
  Id (λ u → Cube n A ∙ u !₀) {u₀} {u₁} u₂ (u₀ !⁰) (u₁ !⁰)
‼⁰ (a₀₀ , a₁₀ , a₂₀ , b₀₀ , b₁₀) (a₀₁ , a₁₁ , a₂₁ , b₀₁ , b₁₁) (a₀₂ , a₁₂ , a₂₂ , b₀₂ , b₁₂) = b₀₂

‼¹ : {n : ℕᵉ} {A : Type} (u₀ u₁ : ∂ (𝐬 n) A) (u₂ : u₀ ＝ u₁) →
  Id (λ u → Cube n A ∙ u !₁) {u₀} {u₁} u₂ (u₀ !¹) (u₁ !¹)
‼¹ (a₀₀ , a₁₀ , a₂₀ , b₀₀ , b₁₀) (a₀₁ , a₁₁ , a₂₁ , b₀₁ , b₁₁) (a₀₂ , a₁₂ , a₂₂ , b₀₂ , b₁₂) = b₁₂

postulate
  ap-!⁰ : {n : ℕᵉ} {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 n) A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → u δ !⁰) δ₂ ≡ ‼⁰ (u δ₀) (u δ₁) (ap u δ₂)
  ap-!¹ : {n : ℕᵉ} {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 n) A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → u δ !¹) δ₂ ≡ ‼¹ (u δ₀) (u δ₁) (ap u δ₂)
  refl-!⁰ : {n : ℕᵉ} {A : Type} (u : ∂ (𝐬 n) A) →
    refl (u !⁰) ≡ ‼⁰ u u (refl u)
  refl-!¹ : {n : ℕᵉ} {A : Type} (u : ∂ (𝐬 n) A) →
    refl (u !¹) ≡ ‼¹ u u (refl u)
{-# REWRITE ap-!⁰ ap-!¹ refl-!⁰ refl-!¹ #-}

----------------------------------------
-- Special cases for concrete n
----------------------------------------

-- When n is concrete, then (∂ (𝐬 n) A) reduces further, and the above
-- rewrites may not fire.  We can partially work around this by
-- declaring some of them manually, like these.

ap-!⁰-𝐳 : {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 𝐳) A)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  ap (λ δ → u δ !⁰) δ₂ ≡ ‼⁰ (u δ₀) (u δ₁) (ap u δ₂)
ap-!⁰-𝐳 u δ₂ = ap-!⁰ u δ₂

ap-!¹-𝐳 : {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 𝐳) A)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  ap (λ δ → u δ !¹) δ₂ ≡ ‼¹ (u δ₀) (u δ₁) (ap u δ₂)
ap-!¹-𝐳 u δ₂ = ap-!¹ u δ₂

refl-!⁰-𝐳 : {A : Type} (u : ∂ (𝐬 𝐳) A) →
  refl (u !⁰) ≡ ‼⁰ u u (refl u)
refl-!⁰-𝐳 u = refl-!⁰ u

refl-!¹-𝐳 : {A : Type} (u : ∂ (𝐬 𝐳) A) →
  refl (u !¹) ≡ ‼¹ u u (refl u)
refl-!¹-𝐳 u = refl-!¹ u

{-# REWRITE ap-!⁰-𝐳 ap-!¹-𝐳 refl-!⁰-𝐳 refl-!¹-𝐳 #-}

-- You might think we want these too.  First of all, they require
-- corr-refl-⊤ to typecheck.  (It's in the hidden type of the ≡.)
ap-!₀-𝐳 : {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 𝐳) A)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  ap (λ δ → u δ !₀) δ₂ ≡ ‼₀ (u δ₀) (u δ₁) (ap u δ₂)
ap-!₀-𝐳 u δ₂ = ap-!₀ {𝐳} u δ₂

ap-!₁-𝐳 : {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 𝐳) A)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  ap (λ δ → u δ !₁) δ₂ ≡ ‼₁ (u δ₀) (u δ₁) (ap u δ₂)
ap-!₁-𝐳 u δ₂ = ap-!₁ u δ₂

ap-!₂-𝐳 : {A : Type} {Δ : Type} (u : Δ → ∂ (𝐬 𝐳) A)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  ap (λ δ → u δ !₂) δ₂ ≡ ‼₂ (u δ₀) (u δ₁) (ap u δ₂)
ap-!₂-𝐳 u δ₂ = ap-!₂ u δ₂

-- But secondly, they aren't legal rewrites, and they aren't
-- necessary.  They aren't necessary because (with corr-refl-⊤) they
-- are rewriting elements of ⊤, and because of the η-rule for ⊤ all
-- elements of it are equal anyway.  I think they aren't legal for the
-- same reason: they "don't bind u and A", even though u and A are
-- apparently present in the LHS, because it belongs to ⊤ and
-- rewriting happens modulo η, so they could theoretically be trying
-- to rewrite *anything at all*.

--{-# REWRITE ap-!₀-𝐳 ap-!₁-𝐳 ap-!₂-𝐳 #-}
