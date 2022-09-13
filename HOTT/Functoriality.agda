{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Functoriality where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe.Parametric

------------------------------
-- ap-snd and ap-, and ap-∙
------------------------------

-- Now that we can compute ＝ and Id using maps into the universe, we
-- can tackle these super-difficult aps.  The problem with all of them
-- is that their well-typedness seems to depend on themselves.
-- However, we can convince Agda to accept them if we build up in
-- stages, first asserting simpler versions with less type dependency.
-- We also have to interleave this process for all three of them,
-- since they depend on each other as well.

-- We also frequently use the following trick.  Rules like ap-∙ only
-- fire on terms that belong to a ⇒ and are applied with ∙, but for
-- general rewriting we need these rules to apply to arbitrary type
-- families that belong to a →.  So we first define an element of the
-- type we need under the assumption of a ⇒ type family, and then in
-- the actual rewrite rule we hand off with a 𝛌-abstraction.

-- The simplest form of ap-∙ is for non-dependent functions between
-- constant types.  In this case we don't need the above trick at all.
postulate
  ap-∙¹ : {Δ A B : Type}
    (f : (δ : Δ) → A ⇒ B) (a : (δ : Δ) → A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡ ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂)
{-# REWRITE ap-∙¹ #-}

-- With this, we can state ap-snd for non-dependent pairs (in
-- nonconstant type families).
frob-ap-snd¹ : {Δ : Type} (A B : Δ ⇒ Type) (u : (δ : Δ) → (A ∙ δ) × (B ∙ δ))
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (B ∙_) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd¹ A B u {δ₀} {δ₁} δ₂ = snd (ap u δ₂) 

postulate
  ap-snd¹ : {Δ : Type} {A B : Δ → Type} (u : (δ : Δ) → A δ × B δ)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡  frob-ap-snd¹ (𝛌 A) (𝛌 B) u δ₂
{-# REWRITE ap-snd¹ #-}

-- This, in turn, allows stating ap-∙ for *dependent* functions in a
-- constant type family, and similarly ap-, for dependent pairs in a
-- constant type family.
frob-ap-∙² : {Δ A : Type} (B : A ⇒ Type)
  (f : (δ : Δ) → Π A (B ∙_)) (a : (δ : Δ) → A)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ (a z)) δ₂ (f δ₀ ∙ a δ₀) (f δ₁ ∙ a δ₁)
frob-ap-∙² {Δ} {A} B f a {δ₀} {δ₁} δ₂ = ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂)

frob-ap-,² : {Δ A : Type} (B : A ⇒ Type)
  (a : (x : Δ) → A) (b : (x : Δ) → B ∙ (a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id {Δ × A} (λ u → B ∙ (snd u)) {δ₀ , a δ₀} {δ₁ , a δ₁} (δ₂ , ap a δ₂) (b δ₀) (b δ₁)
frob-ap-,² B a b δ₂ = ap b δ₂

postulate
  ap-∙² : {Δ A : Type} (B : A → Type)
    (f : (δ : Δ) → Π A B) (a : (δ : Δ) → A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡ frob-ap-∙² (𝛌 B) f a δ₂
  ap-,² : {Δ A : Type} (B : A → Type)
    (a : (x : Δ) → A) (b : (x : Δ) → B (a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ x → (_,_ {A} {B} (a x) (b x))) δ₂ ≡
      (ap a δ₂ , frob-ap-,² (𝛌 B) a b δ₂)
{-# REWRITE ap-∙² ap-,² #-}

-- Now we can handle the fully general ap-, for dependent pairs in a
-- non-constant type family, and also ap-snd for dependent pairs in a
-- constant type family.
frob-ap-, : {Δ : Type} (A : Δ ⇒ Type) (B : Σ Δ (A ∙_) ⇒ Type)
  (a : (x : Δ) → A ∙ x) (b : (x : Δ) → B ∙ (x , a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (B ∙_) (δ₂ , ap a δ₂) (b δ₀) (b δ₁)
frob-ap-, A B a b δ₂ = ap b δ₂

frob-ap-snd² : {Δ A : Type} (B : A ⇒ Type)
  (u : (δ : Δ) → Σ A (B ∙_)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ (fst (u z))) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd² B u δ₂ = snd (ap u δ₂)

postulate
  ap-, : {Δ : Type} (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (a : (x : Δ) → A x) (b : (x : Δ) → B x (a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ x → (_,_ {A x} {B x} (a x) (b x))) δ₂ ≡
      (ap a δ₂ , frob-ap-, (𝛌 A) (ƛ z ⇒ B (fst z) (snd z)) a b δ₂)
  ap-snd² : {Δ A : Type} (B : A → Type)
    (u : (δ : Δ) → Σ A B) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ frob-ap-snd² (𝛌 B) u δ₂
{-# REWRITE ap-, ap-snd² #-}

-- Next is the fully general ap-∙ for dependent functions in a
-- non-constant type family.
frob-ap-∙ : {Δ : Type} (A : Δ ⇒ Type) (B : Σ Δ (A ∙_) ⇒ Type)
  (f : (δ : Δ) → Π (A ∙ δ) (λ x → B ∙ (δ , x))) (a : (δ : Δ) → A ∙ δ)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ (z , a z)) δ₂ (f δ₀ ∙ a δ₀) (f δ₁ ∙ a δ₁)
frob-ap-∙ {Δ} A B f a {δ₀} {δ₁} δ₂ = ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂)

postulate
  ap-∙ : {Δ : Type} {A : Δ → Type} {B : (δ : Δ) → A δ → Type}
    (f : (δ : Δ) → Π (A δ) (B δ)) (a : (δ : Δ) → A δ)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡
      frob-ap-∙ (𝛌 A) (ƛ z ⇒ B (fst z) (snd z)) f a δ₂
{-# REWRITE ap-∙ #-}

-- And finally, we can deal with fully general ap-snd, for dependent
-- pairs in a non-constant type family.
frob-ap-snd : {Δ : Type} (A : Δ ⇒ Type) (B : （ x ⦂ Δ ）⇒ A ∙ x ⇒ Type)
  (u : (δ : Δ) → Σ (A ∙ δ) (B ∙ δ ∙_)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ z ∙ (fst (u z))) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd A B u δ₂ = snd (ap u δ₂)

postulate
  ap-snd : {Δ : Type} (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (u : (δ : Δ) → Σ (A δ) (B δ)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ frob-ap-snd (𝛌 A) (ƛ δ ⇒ ƛ a ⇒ B δ a) u δ₂
{-# REWRITE ap-snd #-}

------------------------------
-- ap-corr
------------------------------

-- With these rules for ap available, we can now postulate ap-corr.
-- This requires the implicit equality argument to corr to eliminate
-- green slime and fire, since the codomain of the "ap" may in
-- practice be a reduced version of Corr rather than Corr itself.
-- Since these equalities are under a binder in ap-corr, we need to
-- apply funextᵉ before we can destruct them in the output; for this
-- we use an auxiliary function.

frob-ap-corr : {n : ℕᵉ} {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
  (A : Δ → CUBE n Type) {Ω : Δ → Type} (ω : (λ δ → Corr n ∙ fst (A δ)) ≡ Ω) →
  Id Ω δ₂ (corr (A δ₀) ⦃ happlyᵉ ω δ₀ ⦄) (corr (A δ₁) ⦃ happlyᵉ ω δ₁ ⦄)
frob-ap-corr {n} {Δ} {δ₀} {δ₁} δ₂ A reflᵉ =
  coeʰ-Id (Corr n ∙_) {δ₂ = ap (λ x → fst (A x)) δ₂} reflᵉ reflᵉ reflʰ
    (cong (λ x → corr x ⦃ reflᵉ ⦄) (ηΣ _ (A δ₀)) )
    (cong (λ x → corr x ⦃ reflᵉ ⦄) (ηΣ _ (A δ₁)) )
    (fst (corr {𝐬 n}
      ((fst (A δ₀) , fst (A δ₁)  , fst (ap A δ₂) ,
        snd (A δ₀) , snd (A δ₁)) , snd (ap A δ₂)) ⦃ reflᵉ ⦄))

postulate
  ap-corr : {n : ℕᵉ} {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (A : Δ → CUBE n Type) {Ω : Δ → Type} (ω : (δ : Δ) → Corr n ∙ fst (A δ) ≡ Ω δ) →
    ap (λ δ → corr {n} (A δ) ⦃ ω δ ⦄) δ₂ ≡ frob-ap-corr δ₂ A (funextᵉ ω) 
{-# REWRITE ap-corr #-}
