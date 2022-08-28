{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Id where

open import HOTT.Base

infix  35 _＝_

------------------------------
-- Homogeneous Id and refl
------------------------------

postulate
  _＝_ : {A : Type} → A → A → Type
  refl : {A : Type} (a : A) → (a ＝ a)

------------------------------
-- Dependent identity types
------------------------------

postulate
  Id : {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B a₀) (b₁ : B a₁) → Type
  -- Id-idmap comes later, as it requires the universe
  Id-const : (A B : Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    Id {A} (λ _ → B) a₂ ≡ _＝_ {B}
  -- This should follow from the definitions in most concrete cases.
  -- I'm not sure about Id-＝ for a variable type; see Id-refl, and
  -- ap-refl, later on.
  Id-refl : {A : Type} (B : A → Type) {a : A} →
    Id B (refl a) ≡ _＝_ {B a}
{-# REWRITE Id-const Id-refl #-}

postulate
  ap : {A : Type} {B : A → Type} (f : (x : A) → B x)
    {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → Id B a₂ (f a₀) (f a₁)
  ap-idmap : {A : Type} {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    ap {A} (λ x → x) a₂ ≡ a₂
  ap-const : {A B : Type} (b : B) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    ap {A} (λ _ → b) a₂ ≡ refl b
  -- This should also be admissible in most concrete cases.
  ap-refl : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) →
    ap f (refl a) ≡ refl (f a)
{-# REWRITE ap-const ap-idmap ap-refl #-}

----------------------------------------
-- Identifications and refl in ⊤
----------------------------------------

postulate
  ＝-⊤ : (u v : ⊤) → (u ＝ v) ≡ ⊤
{-# REWRITE ＝-⊤ #-}
postulate
  refl★ : refl ★ ≡ ★
{-# REWRITE refl★ #-}

--------------------------------------------------
-- Identifications, refl, and ap in Σ-types
--------------------------------------------------

postulate
  ＝-Σ : {A : Type} {B : A → Type} (u v : Σ A B) →
    (u ＝ v) ≡ （ p ⦂ fst u ＝ fst v ）× Id B p (snd u) (snd v)
{-# REWRITE ＝-Σ #-}

postulate
  refl-, : {A : Type} {B : A → Type} (a : A) (b : B a) →
    refl {Σ A B} (a , b) ≡ (refl a , refl b)
{-# REWRITE refl-, #-}

-- We want to rewrite (refl (snd u)) to (snd (refl u)), but this isn't
-- well-typed, because refl-fst and Id-refl are not confluent:
--- (refl (snd u)) has type (fst u ＝ fst u)
--- (snd (refl u)) has type (Id B (fst (refl u)) (snd u) (snd u))
-- and these are not convertible by Agda, even though they are both
-- reducts of (Id B (refl (fst u)) (snd u) (snd u)), the first by
-- Id-refl and the second by refl-fst.

-- To work around this, we use the trick of declaring a rewrite in
-- between the type signature of a function and its definition.
-- Specifically, we give a name to the putative result of refl-snd,
-- giving it the type that reduces to the two incompatible things.
frob-refl-snd : {A : Type} {B : A → Type} (u : Σ A B) →
  Id B (refl (fst u)) (snd u) (snd u)

postulate
  refl-fst : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (fst u) ≡ fst (refl u)
  -- Since we haven't declared refl-fst to be a rewrite yet at this
  -- point, the type of frob-refl-snd reduces to (snd u ＝ snd u) by
  -- Id-refl, so that it's well-typed here.
  refl-snd : {A : Type} {B : A → Type} (u : Σ A B) →
    refl (snd u) ≡ frob-refl-snd u

{-# REWRITE refl-fst refl-snd #-}

-- Now after refl-fst is declared a rewrite, the type of frob-refl-snd
-- u reduces instead to (Id B (fst (refl u)) (snd u) (snd u)), so that
-- we can give (snd (refl u)) as its definition.
frob-refl-snd u = snd (refl u)

uncurry : {T : Type} {Δ : Type} {A : Δ → Type} (B : (x : Δ) → A x → T) → Σ Δ A → T
uncurry B u = B (fst u) (snd u)

module _ (Δ : Type) (A : Δ → Type) (B : (x : Δ) → A x → Type) where
  IdΣ : (δ₀ δ₁ : Δ) (δ₂ : δ₀ ＝ δ₁) (u₀ : Σ (A δ₀) (B δ₀)) (u₁ : Σ (A δ₁) (B δ₁)) → Type
  IdΣ δ₀ δ₁ δ₂ u₀ u₁ =
    （ a₂ ⦂ Id A δ₂ (fst u₀) (fst u₁) ）×
      Id {Σ Δ A} (uncurry B) {δ₀ , fst u₀} {δ₁ , fst u₁} (δ₂ , a₂) (snd u₀) (snd u₁)

  postulate
    Id-Σ : {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (u₀ : Σ (A δ₀) (B δ₀)) (u₁ : Σ (A δ₁) (B δ₁)) →
      Id (λ x → Σ (A x) (B x)) δ₂ u₀ u₁ ≡ IdΣ δ₀ δ₁ δ₂ u₀ u₁
  {-# REWRITE Id-Σ #-}

  postulate
    ap-fst : (u : (δ : Δ) → Σ (A δ) (B δ)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
      ap (λ δ → fst (u δ)) δ₂ ≡ fst (ap u δ₂)
    {-# REWRITE ap-fst #-}

-- ap-, and ap-snd are very difficult to define, so we postpone them to later.

------------------------------
-- Bundled identity types
------------------------------

-- TODO: Find a consistent naming scheme for these.

ID : Type → Type
ID A = （ a₀ ⦂ A ）× （ a₁ ⦂ A ）× a₀ ＝ a₁

IDᵈ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) → Type
IDᵈ A {δ₀} {δ₁} δ₂ = （ a₀ ⦂ A δ₀ ）× （ a₁ ⦂ A δ₁ ）× Id A δ₂ a₀ a₁

ID× : {A : Type} (B : A ⇒ Type) → Type
ID× {A} B = （ a₀ ⦂ A ）× （ a₁ ⦂ A ）× （ a₂ ⦂ a₀ ＝ a₁ ）× B ∙ a₀ × B ∙ a₁

Idᵈ : {A : Type} (B : A ⇒ Type) → ID× B → Type
Idᵈ {A} B u = Id (B ∙_) (₃rd u) (₄th u) (₅th' u)

--------------------------------------------------
-- Identifications, refl, and ap in Π-types
--------------------------------------------------

postulate
  ＝-Π : {A : Type} {B : A → Type} (f g : Π A B) →
    (f ＝ g) ≡ （ aₓ ⦂ ID A ）⇒ Id B (₃rd' aₓ) (f ∙ ₁st aₓ) (g ∙ ₂nd aₓ)
{-# REWRITE ＝-Π #-}

postulate
  refl-ƛ : {A : Type} {B : A → Type} (f : (x : A) → B x) (aₓ : ID A) →
    refl (𝛌 f) ∙ aₓ ≡ ap f (₃rd' aₓ)
  refl-∙ : {A : Type} {B : A → Type} (f : Π A B) (a : A) →
    refl (f ∙ a) ≡ refl f ∙ (a , a , refl a)
{-# REWRITE refl-ƛ refl-∙ #-}

IdΠ : (Δ : Type) (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (δ₀ δ₁ : Δ) (δ₂ : δ₀ ＝ δ₁) (f₀ : Π (A δ₀) (B δ₀)) (f₁ : Π (A δ₁) (B δ₁)) →
    Type
IdΠ Δ A B δ₀ δ₁ δ₂ f₀ f₁ =
  （ aₓ ⦂ IDᵈ A δ₂ ）⇒
    Id {Σ Δ A} (uncurry B) {δ₀ , ₁st aₓ} {δ₁ , ₂nd aₓ} (δ₂ , ₃rd' aₓ)
      (f₀ ∙ ₁st aₓ) (f₁ ∙ ₂nd aₓ)

postulate
  Id-Π : {Δ : Type} {A : Δ → Type} {B : (x : Δ) → A x → Type}
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (f₀ : Π (A δ₀) (B δ₀)) (f₁ : Π (A δ₁) (B δ₁)) →
    Id (λ x → Π (A x) (B x)) δ₂ f₀ f₁ ≡ IdΠ Δ A B δ₀ δ₁ δ₂ f₀ f₁
{-# REWRITE Id-Π #-}

postulate
  ap-ƛ : {Δ : Type} (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (f : (δ : Δ) (a : A δ) → B δ a)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) (aₓ : IDᵈ A δ₂) →
    ap (λ x → ƛ y ⇒ f x y) δ₂ ∙ aₓ ≡
    ap {Σ Δ A} (λ z → f (fst z) (snd z)) {δ₀ , ₁st aₓ} {δ₁ , ₂nd aₓ} (δ₂ , ₃rd' aₓ)
{-# REWRITE ap-ƛ #-}

-- ap-∙ is very difficult to define, so we postpone it to later.
