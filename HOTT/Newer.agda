{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Newer where

open import Agda.Primitive renaming (Set to Type; SSet to Typeᵉ) public

infixl 40 _∙_ _∙'_ _∘_
infix  35 _＝_
infixr 35 _×_
infixr 30 _,_ Σ _⇒_ Π
infixr 20 𝛌 𝛌'
infix  10 _≡_ _≡ᵉ_

------------------------------
-- Strict equality
------------------------------

-- Because we don't assume cumulativity, we have two strict
-- equalities, one for elements of types and one for elements of
-- exotypes.  We decorate operations involving the first with ᶠ (for
-- fibrant) and the second with ᵉ.  The exception is the equality type
-- itself, where we write ≡ instead of ≡ᶠ.

data _≡_ {A : Type} (a : A) : A → Typeᵉ where
  reflᵉ : a ≡ a

data _≡ᵉ_ {A : Typeᵉ} (a : A) : A → Typeᵉ where
  reflᵉᵉ : a ≡ᵉ a

{-# BUILTIN REWRITE _≡_ #-}
{-# BUILTIN REWRITE _≡ᵉ_ #-}

------------------------------
-- Homogeneous Id and refl
------------------------------

postulate
  _＝_ : {A : Type} → A → A → Type
  refl : {A : Type} (a : A) → (a ＝ a)

----------------------------------------
-- Unit type and its identifications
----------------------------------------

record ⊤ : Type where
  constructor ★

open ⊤

postulate
  ＝-⊤ : (u v : ⊤) → (u ＝ v) ≡ ⊤

{-# REWRITE ＝-⊤ #-}

postulate
  refl★ : refl ★ ≡ ★

{-# REWRITE refl★ #-}

--------------------
-- Σ-types
--------------------

postulate
  Σ : (A : Type) (B : A → Type) → Type
  _,_ : {A : Type} {B : A → Type} (a : A) → B a → Σ A B

syntax Σ A (λ x → B) = （ x ⦂ A ）× B

postulate
  fst : {A : Type} {B : A → Type} → Σ A B → A
  snd : {A : Type} {B : A → Type} (u : Σ A B) → B (fst u)
  Ση : (A : Type) (B : A → Type) (u : Σ A B) → (fst u , snd u) ≡ u
  fstβ : {A : Type} {B : A → Type} (a : A) (b : B a) → fst {A} {B} (a , b) ≡ a

{-# REWRITE Ση fstβ #-}

postulate
  sndβ : {A : Type} {B : A → Type} (a : A) (b : B a) → snd {A} {B} (a , b) ≡ b

{-# REWRITE sndβ #-}

₁st : {A : Type} {B : A → Type} → （ x ⦂ A ）× B x → A
₁st u = fst u

₂nd' : {A : Type} {B : A → Type} → (u : （ x ⦂ A ）× B x) → B (₁st u)
₂nd' u = snd u

₂nd : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× C x y) → B (₁st u)
₂nd u = fst (snd u)

₃rd' : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× C x y) → C (₁st u) (₂nd u)
₃rd' u = snd (snd u)

₃rd : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} {D : (x : A) (y : B x) → C x y → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× （ z ⦂ C x y ）× D x y z) → C (₁st u) (₂nd u)
₃rd u = fst (snd (snd u))

₄th' : {A : Type} {B : A → Type} {C : (x : A) → B x → Type} {D : (x : A) (y : B x) → C x y → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× （ z ⦂ C x y ）× D x y z) → D (₁st u) (₂nd u) (₃rd u)
₄th' u = snd (snd (snd u))

₄th : {A : Type} {B : A → Type} {C : (x : A) → B x → Type}
  {D : (x : A) (y : B x) → C x y → Type} {E : (x : A) (y : B x) (z : C x y) → D x y z → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× （ z ⦂ C x y ）× （ w ⦂ D x y z ）× E x y z w) →
  D (₁st u) (₂nd u) (₃rd u)
₄th u = fst (snd (snd (snd u)))

₅th' : {A : Type} {B : A → Type} {C : (x : A) → B x → Type}
  {D : (x : A) (y : B x) → C x y → Type} {E : (x : A) (y : B x) (z : C x y) → D x y z → Type} →
  (u : （ x ⦂ A ）× （ y ⦂ B x ）× （ z ⦂ C x y ）× （ w ⦂ D x y z ）× E x y z w) →
  E (₁st u) (₂nd u) (₃rd u) (₄th u)
₅th' u = snd (snd (snd (snd u)))

----------------------------------------
-- Non-dependent product types
----------------------------------------

_×_ : Type → Type → Type
A × B = （ _ ⦂ A ）× B

--------------------
-- Π-types
--------------------

postulate
  Π : (A : Type) (B : A → Type) → Type
  𝛌 : {A : Type} {B : A → Type} (f : (x : A) → B x) → Π A B

syntax Π A (λ x → B) = （ x ⦂ A ）⇒ B
syntax 𝛌 (λ x → f) = ƛ x ⇒ f

-- It's tempting to try to make Π a record type, with 𝛌 a constructor
-- and _∙_ a field.  But then _∙_ doesn't store A and B as implicit
-- arguments, which means that refl-∙ can't bind them.
postulate
  -- TODO: Add an equality to _∙_ so that rules like refl-ƛ can fire.
  _∙_ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → B a
  Πβ : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) → (𝛌 f ∙ a) ≡ f a
  Πη : {A : Type} {B : A → Type} (f : Π A B) → (ƛ x ⇒ f ∙ x) ≡ f

{-# REWRITE Πβ Πη #-}

----------------------------------------
-- Non-dependent function types
----------------------------------------

postulate
  _⇒_ : Type → Type → Type
  𝛌' : {A B : Type} (f : A → B) → A ⇒ B

syntax 𝛌' (λ x → f) = ƛ' x ⇒ f

postulate
  _∙'_ : {A B : Type} (f : A ⇒ B) (a : A) → B
  ⇒β : {A B : Type} (f : A → B) (a : A) → (𝛌' f ∙' a) ≡ f a
  ⇒η : {A B : Type} (f : A ⇒ B) → (ƛ' x ⇒ f ∙' x) ≡ f

{-# REWRITE ⇒β ⇒η #-}

{-
_⇒_ : Type → Type → Type
A ⇒ B = （ x ⦂ A ）⇒ B
-}

_∘_ : {A B C : Type} (g : B ⇒ C) (f : A ⇒ B) → (A ⇒ C)
g ∘ f = ƛ' x ⇒ g ∙' (f ∙' x)

idmap : (A : Type) → (A ⇒ A)
idmap A = ƛ' x ⇒ x

--------------------------------------------------
-- Dependent identity types (declaration)
--------------------------------------------------

postulate
  -- (Far) below we will give a simple "definition" of Id with a
  -- rewrite.  So we could make it an ordinary function, with type
  -- declaration here and definition below.  But that makes the entire
  -- block in between the two a mutual definition, which is
  -- psychologically a bit much; plus it makes the termination checker
  -- complain.
  Id : {A : Type} (B : A ⇒ Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B ∙' a₀) (b₁ : B ∙' a₁) → Type
  -- These will follow from the definition of Id, but for now we make
  -- them rewrites in order to make other stuff well-typed.
  Id-const : (A B : Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ b₁ : B) →
    Id {A} (ƛ' _ ⇒ B) a₂ b₀ b₁ ≡ (b₀ ＝ b₁) 
  Id-refl : {A : Type} (B : A ⇒ Type) {a : A} (b₀ b₁ : B ∙' a) →
    Id B (refl a) b₀ b₁ ≡ (b₀ ＝ b₁)

{-# REWRITE Id-const Id-refl #-}

postulate
  ap : {A : Type} {B : A → Type} (f : (x : A) → B x)
    {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → Id (𝛌' B) a₂ (f a₀) (f a₁)
  ap-const : {A B : Type} (b : B) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    ap {A} (λ _ → b) a₂ ≡ refl b
  -- This should also follow from the definitions in concrete cases.
  ap-refl : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) →
    ap f (refl a) ≡ refl (f a)

{-# REWRITE ap-const ap-refl #-}

------------------------------
-- Identifications in Σ-types
------------------------------

postulate
  ＝-Σ : {A : Type} {B : A → Type} (u v : Σ A B) →
    (u ＝ v) ≡ （ p ⦂ fst u ＝ fst v ）× Id (𝛌' B) p (snd u) (snd v)

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
  Id (𝛌' B) (refl (fst u)) (snd u) (snd u)

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

-- This will be part of the definition of ap-Σ, once Id is defined.
IdΣ : (Δ : Type) (A : Δ → Type) (B : (x : Δ) → A x → Type)
      (δ₀ δ₁ : Δ) (δ₂ : δ₀ ＝ δ₁) (u₀ : Σ (A δ₀) (B δ₀)) (u₁ : Σ (A δ₁) (B δ₁)) →
      Type
IdΣ Δ A B δ₀ δ₁ δ₂ u₀ u₁ =
  （ a₂ ⦂ Id (𝛌' A) δ₂ (fst u₀) (fst u₁) ）×
    Id {Σ Δ A} (ƛ' y ⇒ B (fst y) (snd y)) {δ₀ , fst u₀} {δ₁ , fst u₁} (δ₂ , a₂) (snd u₀) (snd u₁)

postulate
  Id-Σ : {Δ : Type} {A : Δ → Type} {B : (x : Δ) → A x → Type}
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (u₀ : Σ (A δ₀) (B δ₀)) (u₁ : Σ (A δ₁) (B δ₁)) →
    Id (ƛ' x ⇒ Σ (A x) (B x)) δ₂ u₀ u₁ ≡ IdΣ Δ A B δ₀ δ₁ δ₂ u₀ u₁

{-# REWRITE Id-Σ #-}

------------------------------
-- Identifications in Π-types
------------------------------

ID : Type → Type
ID A = （ a₀ ⦂ A ）× （ a₁ ⦂ A ）× a₀ ＝ a₁

postulate
  ＝-⇒ : {A B : Type} (f g : A ⇒ B) →
    (f ＝ g) ≡ （ aₓ ⦂ ID A ）⇒ (f ∙' ₁st aₓ ＝ g ∙' ₂nd aₓ)
  ＝-Π : {A : Type} {B : A → Type} (f g : Π A B) →
    (f ＝ g) ≡ （ aₓ ⦂ ID A ）⇒ Id (𝛌' B) (₃rd' aₓ) (f ∙ ₁st aₓ) (g ∙ ₂nd aₓ)

{-# REWRITE ＝-⇒ ＝-Π #-}

postulate
  refl-ƛ : {A : Type} {B : A → Type} (f : (x : A) → B x) (aₓ : ID A) →
    refl (𝛌 f) ∙ aₓ ≡ ap f (₃rd' aₓ)
  refl-∙ : {A : Type} {B : A → Type} (f : Π A B) (a : A) →
    refl (f ∙ a) ≡ refl f ∙ (a , a , refl a)

--{-# REWRITE refl-ƛ refl-∙ #-}
{-
-- This will eventually follow from the definition of Id and ap-Σ.
IdΠ : (Δ : Type) (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (δ₀ δ₁ : Δ) (δ₂ : δ₀ ＝ δ₁) (f₀ : Π (A δ₀) (B δ₀)) (f₁ : Π (A δ₁) (B δ₁)) →
    Type
IdΠ Δ A B δ₀ δ₁ δ₂ f₀ f₁ =
  （ aₓ ⦂ （ a₀ ⦂ A δ₀ ）× （ a₁ ⦂ A δ₁ ）× Id (𝛌 A) δ₂ a₀ a₁ ）⇒
    Id {Σ Δ A} (ƛ y ⇒ B (fst y) (snd y)) {δ₀ , ₁st aₓ} {δ₁ , ₂nd aₓ} (δ₂ , ₃rd' aₓ)
      (f₀ ∙ ₁st aₓ) (f₁ ∙ ₂nd aₓ)

postulate
  Id-Π : {Δ : Type} {A : Δ → Type} {B : (x : Δ) → A x → Type}
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (f₀ : Π (A δ₀) (B δ₀)) (f₁ : Π (A δ₁) (B δ₁)) →
    Id (ƛ x ⇒ Π (A x) (B x)) δ₂ f₀ f₁ ≡ IdΠ Δ A B δ₀ δ₁ δ₂ f₀ f₁
-}
--{-# REWRITE Id-Π #-}

{-
  ap-Π
  ap-ƛ
  ap-∙
-}

------------------------------
-- Squares and symmetry
------------------------------
{-
Sq : (A : Type)
  {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
  (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) → Type
Sq A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id {A × A} (ƛ u ⇒ fst u ＝ snd u)
    {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) a₂₀ a₂₁

postulate
  sym : (A : Type)
    {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁)
    {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
    (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
    Sq A a₀₂ a₁₂ a₂₀ a₂₁ → Sq A a₂₀ a₂₁ a₀₂ a₁₂
-}
------------------------------
-- Amazing right adjoints
------------------------------

postulate
  √ : {I : Type} (A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) → I → Type
  dig : {I : Type} (A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type)
    {i₀ i₁ : I} (i₂ : i₀ ＝ i₁)
    (s₀ : √ A i₀) (s₁ : √ A i₁) (s₂ : Id (𝛌' (√ A)) i₂ s₀ s₁) →
    A i₀ i₁ i₂

{-
postulate
  Id-√ : {I : Type} (A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type)
    {i₀ i₁ : I} {i₂ : i₀ ＝ i₁} (s₀ : √ A i₀) (s₁ : √ A i₁) →
    Id (𝛌 (√ A)) i₂ s₀ s₁ ≡
    A i₀ i₁ i₂ ×
    √ {（ i₀ ⦂ I ）× （ i₁ ⦂ I ）× （ i₂ ⦂ i₀ ＝ i₁ ）× √ A i₀ × √ A i₁}
      (λ u₀ u₁ u₂ → Id {（ i₀ ⦂ I ）× （ i₁ ⦂ I ）× (i₀ ＝ i₁)}
                       (ƛ iₓ ⇒ A (fst iₓ) (fst (snd iₓ)) (snd (snd iₓ)))
                       {fst u₀ , fst u₁ , fst u₂}
                       {fst (snd u₀) , fst (snd u₁) , ←Id-const I I (fst u₂) _ _ (fst (snd u₂))}
                       (fst (snd (snd u₀)) , →Id-const I I (fst (snd (snd u₀))) _ _ (fst (snd (snd u₁))) , {!!} )
                       (dig {I} A {fst u₀} {fst u₁} (fst u₂)
                         (fst (snd (snd (snd u₀)))) (fst (snd (snd (snd u₁)))) {!fst (snd (snd (snd u₂)))!} )
                       (dig {I} A {fst (snd u₀)} {fst (snd u₁)} (←Id-const I I (fst u₂) _ _ (fst (snd u₂)))
                         (snd (snd (snd (snd u₀)))) (snd (snd (snd (snd u₁)))) {!snd (snd (snd (snd u₂)))!}))
                       (i₀ , i₁ , i₂ , s₀ , s₁)

{-# REWRITE Id-√ #-}

postulate
  dig-def : {I : Type} {A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {i₀ i₁ : I} (i₂ : i₀ ＝ i₁)
    {s₀ : √ A i₀} {s₁ : √ A i₁} (s₂ : Id (𝛌 (√ A)) i₂ s₀ s₁) →
    dig A i₂ s₀ s₁ s₂ ≡ fst s₂

{-# REWRITE dig-def #-}
-}

------------------------------
-- The universe
------------------------------

btc : (A B : Type) → Type
btc A B = （ tr⇒ ⦂ A ⇒ B ）× （ tr⇐ ⦂ B ⇒ A ）× （ rel ⦂ A ⇒ B ⇒ Type ）×
  (（ x ⦂ A ）⇒ rel ∙' x ∙' (tr⇒ ∙' x)) × ( （ y ⦂ B ）⇒ rel ∙' (tr⇐ ∙' y) ∙' y)

postulate
  corr : (X : Type) → √ (λ X₀ X₁ X₂ → btc X₀ X₁) X

_↓ : {X₀ X₁ : Type} (X₂ : X₀ ＝ X₁) → btc X₀ X₁
_↓ {X₀} {X₁} X₂ = dig (λ X₀ X₁ X₂ → btc X₀ X₁) X₂ (corr X₀) (corr X₁) (ap corr {X₀} {X₁} X₂)

_~[_]_ : {A B : Type} → A → (A ＝ B) → B → Type
a ~[ e ] b = ₃rd (e ↓) ∙' a ∙' b

coe⇒ : {A B : Type} → (A ＝ B) → A ⇒ B
coe⇒ e = ₁st (e ↓)

coe⇐ : {A B : Type} → (A ＝ B) → B ⇒ A
coe⇐ e = ₂nd (e ↓)

~coe⇒ : {A B : Type} (e : A ＝ B) (a : A) → a ~[ e ] coe⇒ e ∙' a
~coe⇒ e a = ₄th (e ↓) ∙ a

~coe⇐ : {A B : Type} (e : A ＝ B) (b : B) → coe⇐ e ∙' b ~[ e ] b
~coe⇐ e b = ₅th' (e ↓) ∙ b

--------------------------------------------------
-- Dependent identity types (definition)
--------------------------------------------------

postulate
  Id-def : {A : Type} (B : A ⇒ Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B ∙' a₀) (b₁ : B ∙' a₁) →
    Id {A} B {a₀} {a₁} a₂ b₀ b₁ ≡ b₀ ~[ refl B ∙ (a₀ , a₁ , a₂) ] b₁

-- Why is this (apparently) causing a rewrite loop?  I guess it's
-- probably the same problem as before, that the type of (refl f)
-- involves (Id (𝛌 B)), which reduces to something involving another
-- (refl (𝛌 B)), whose type also has to be computed.
{-# REWRITE Id-def #-}

tr⇒ : {A : Type} (B : A ⇒ Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → B ∙' a₀ ⇒ B ∙' a₁
tr⇒ {A} B {a₀} {a₁} a₂ = coe⇒ (refl B ∙ (a₀ , a₁ , a₂))

------------------------------
-- refl and ap of Σ-types
------------------------------

postulate
  refl-Σ : (A : Type) (B : A → Type) →
    refl (Σ A B) ↓ ≡ {!!}

------------------------------
-- Ap in Σ-types
------------------------------

{-
postulate
  ap-, : {Δ : Type} {A : Δ → Type} {B : (x : Δ) → A x → Type}
    (a : (x : Δ) → A x) (b : (x : Δ) → B x (a x))
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ x → (_,_ {A x} {B x} (a x) (b x))) δ₂ ≡
    -- Needs Id-AP, which will follow from the definition of Id.
    {!ap a δ₂ , {!ap b δ₂!}!}
-}
{-
  ap-fst
  ap-snd 
-}    

