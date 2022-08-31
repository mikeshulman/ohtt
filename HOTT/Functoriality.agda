{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Functoriality where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube
open import HOTT.Universe

------------------------------
-- Functoriality of Id
------------------------------

-- With the computation rules for Id on application, we can prove that
-- its functoriality holds definitionally.  However, this only holds
-- for ⇒-functions rather than framework →-functions.  Thus, in other
-- situations we may need to apply these coercions manually, wrapping
-- a type family in 𝛌 by hand.
←Id-ap : {A B : Type} (f : A → B) (C : B ⇒ Type)
  {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) {c₀ : C ∙ f a₀} {c₁ : C  ∙ f a₁} →
  Id (λ a → C ∙ f a) a₂ c₀ c₁ → Id (C ∙_) (ap f a₂) c₀ c₁
←Id-ap f C a₂ e = e

→Id-ap : {A B : Type} (f : A → B) (C : B ⇒ Type)
  {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) {c₀ : C ∙ f a₀} {c₁ : C  ∙ f a₁} →
  Id (C ∙_) (ap f a₂) c₀ c₁ → Id (λ a → C ∙ f a) a₂ c₀ c₁
→Id-ap f C a₂ e = e

------------------------------
-- ap-snd and ap-, and ap-∙
------------------------------

-- Now that we have Id-∙ we can tackle these super-difficult aps.  The
-- problem with all of them is that their well-typedness seems to
-- depend on themselves.  However, we can convince Agda to accept them
-- if we build up in stages, first asserting simpler versions with
-- less type dependency.  We also have to interleave this process for
-- all three of them, since they depend on each other as well.

-- We also frequently use the following trick.  The rule Id-∙ only
-- fires on type families that belong to a ⇒ and are applied with ∙,
-- but for general rewriting we need these rules to apply to arbitrary
-- type families that belong to a →.  So we first define an element of
-- the type we need under the assumption of a ⇒ type family, and then
-- in the actual rewrite rule we hand off with a 𝛌-abstraction.
-- (Morally, we are using one of the Id-ap rules from above, but they
-- don't work completely until we have these computation rules for ap
-- in place, so we use special lemmas instead.)

-- First we can state ap-snd for non-dependent product types.
frob-ap-snd¹ : {Δ : Type} (A B : Δ ⇒ Type) (u : (δ : Δ) → (A ∙ δ) × (B ∙ δ))
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (B ∙_) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd¹ A B u {δ₀} {δ₁} δ₂ = snd (ap u δ₂)

postulate
  ap-snd¹ : {Δ : Type} {A B : Δ → Type} (u : (δ : Δ) → A δ × B δ)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ frob-ap-snd¹ (𝛌 A) (𝛌 B) u δ₂
{-# REWRITE ap-snd¹ #-}

-- This allows us to state all three rules for dependent Π- and
-- Σ-types, as long as they don't depend on the context.
frob-ap-snd² : {Δ A : Type} (B : A ⇒ Type)
  (u : (δ : Δ) → Σ A (B ∙_)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ (fst (u z))) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd² B u δ₂ = snd (ap u δ₂)

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
  ap-snd² : {Δ A : Type} (B : A → Type)
    (u : (δ : Δ) → Σ A B) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ frob-ap-snd² (𝛌 B) u δ₂
  ap-∙² : {Δ A : Type} (B : A → Type)
    (f : (δ : Δ) → Π A B) (a : (δ : Δ) → A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡ frob-ap-∙² (𝛌 B) f a δ₂
  ap-,² : {Δ A : Type} (B : A → Type)
    (a : (x : Δ) → A) (b : (x : Δ) → B (a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ x → (_,_ {A} {B} (a x) (b x))) δ₂ ≡ (ap a δ₂ , frob-ap-,² (𝛌 B) a b δ₂)
{-# REWRITE ap-snd² ap-∙² ap-,² #-}

-- These, in turn, allow us to state the general forms of all three rules.
frob-ap-snd : {Δ : Type} (A : Δ ⇒ Type) (B : （ x ⦂ Δ ）⇒ A ∙ x ⇒ Type)
  (u : (δ : Δ) → Σ (A ∙ δ) (B ∙ δ ∙_)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ z ∙ (fst (u z))) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd A B u δ₂ = snd (ap u δ₂)

frob-ap-, : {Δ : Type} (A : Δ ⇒ Type) (B : Σ Δ (A ∙_) ⇒ Type)
  (a : (x : Δ) → A ∙ x) (b : (x : Δ) → B ∙ (x , a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (B ∙_) (δ₂ , ap a δ₂) (b δ₀) (b δ₁)
frob-ap-, A B a b δ₂ = ap b δ₂

frob-ap-∙ : {Δ : Type} (A : Δ ⇒ Type) (B : Σ Δ (A ∙_) ⇒ Type)
  (f : (δ : Δ) → Π (A ∙ δ) (λ x → B ∙ (δ , x))) (a : (δ : Δ) → A ∙ δ)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ (z , a z)) δ₂ (f δ₀ ∙ a δ₀) (f δ₁ ∙ a δ₁)
frob-ap-∙ {Δ} A B f a {δ₀} {δ₁} δ₂ = ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) 

postulate
  ap-snd : {Δ : Type} (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (u : (δ : Δ) → Σ (A δ) (B δ)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ frob-ap-snd (𝛌 A) (ƛ δ ⇒ ƛ a ⇒ B δ a) u δ₂
  ap-, : {Δ : Type} (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (a : (x : Δ) → A x) (b : (x : Δ) → B x (a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ x → (_,_ {A x} {B x} (a x) (b x))) δ₂ ≡ (ap a δ₂ , frob-ap-, (𝛌 A) (ƛ z ⇒ B (fst z) (snd z)) a b δ₂)
  ap-∙ : {Δ : Type} {A : Δ → Type} {B : (δ : Δ) → A δ → Type}
    (f : (δ : Δ) → Π (A δ) (B δ)) (a : (δ : Δ) → A δ)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡ frob-ap-∙ (𝛌 A) (ƛ z ⇒ B (fst z) (snd z)) f a δ₂
{-# REWRITE ap-snd ap-, ap-∙ #-}

----------------------------------------
-- Fancier ap-refl and Id-refl
----------------------------------------

-- The problem with Id-refl and ap-refl as rewrites is that (refl a)
-- is volatile, so it may have already been reduced to something else.
-- This is an issue for squares, which are defined as Id-＝, where I
-- don't know of another way to enforce Id-refl.  The following
-- rewrites allow us to at least break down the case when refl has
-- been reduced to a tuple of refls.

postulate
  ap-refl, : {A : Type} (B : A → Type) (C : Σ A B → Type)
    (f : (x : Σ A B) → C x) (a : A) {b₀ b₁ : B a} (b₂ : b₀ ＝ b₁) →
    ap f {a , b₀} {a , b₁} (refl a , b₂) ≡
    ←Id-ap {B a} {Σ A B} (λ b → (a , b)) (𝛌 C) b₂ (ap (λ y → f (a , y)) b₂)
  Id-refl, : {A : Type} (B : A → Type) (C : Σ A B → Type)
    (a : A) {b₀ b₁ : B a} (b₂ : b₀ ＝ b₁) (c₀ : C (a , b₀)) (c₁ : C (a , b₁)) →
    Id C {a , b₀} {a , b₁} (refl a , b₂) c₀ c₁ ≡ Id (λ b → C (a , b)) {b₀} {b₁} b₂ c₀ c₁
{-# REWRITE ap-refl, Id-refl, #-}

-- This isn't perfect, even when considering tuples, since it doesn't
-- deal with cases like ((refl a , b₂) , c₂), which arise naturally
-- due to (for instance) ap-ƛ.  This would be an advantage of using
-- telescopes instead of Σ-types, since a telescope can be maintained
-- as right-associated even when extending it on the right.

--------------------
-- ap-kan
--------------------

-- Now that we have Id-ap, we can postulate ap-kan.  This requires the
-- equality in kan to eliminate green slime and fire, since the
-- codomain of the "ap" may in practice be a reduced version of Kan
-- rather than Kan itself.  Since these equalities are under a binder,
-- we need to apply funextᵉ before we can destruct them in the output;
-- for this we use an auxiliary function.

frob-ap-kan : {n : ℕᵉ} {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
  (A : Δ → CUBE n Type) {Ω : Δ → Type} (ω : (λ δ → Kan n ∙ fst (A δ)) ≡ Ω) →
  Id Ω δ₂ (kan (A δ₀) ⦃ happlyᵉ ω δ₀ ⦄) (kan (A δ₁) ⦃ happlyᵉ ω δ₁ ⦄)
frob-ap-kan {n} {Δ} {δ₀} {δ₁} δ₂ A reflᵉ =
  →Id-ap (λ x → fst (A x)) (Kan n) δ₂
    (coeʰ-Id (Kan n ∙_) {δ₂ = ap (λ x → fst (A x)) δ₂} reflᵉ reflᵉ reflʰ
      (cong (λ x → kan x ⦃ reflᵉ ⦄) (ηΣ _ (A δ₀)) )
      (cong (λ x → kan x ⦃ reflᵉ ⦄) (ηΣ _ (A δ₁)) )
      (fst (kan {𝐬 n}
        (fst (A δ₀) ⸴ fst (A δ₁) ⸴ fst (ap A δ₂) ⸴ snd (A δ₀) ⸴ snd (A δ₁) , snd (ap A δ₂)) ⦃ reflᵉ ⦄)))

postulate
  ap-kan : {n : ℕᵉ} {Δ : Type} {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (A : Δ → CUBE n Type) {Ω : Δ → Type} (ω : (δ : Δ) → Kan n ∙ fst (A δ) ≡ Ω δ) →
    ap (λ δ → kan {n} (A δ) ⦃ ω δ ⦄) δ₂ ≡ frob-ap-kan δ₂ A (funextᵉ ω)
{-# REWRITE ap-kan #-}
