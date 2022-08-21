{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like --experimental-lossy-unification #-}

module HOTT.Newer where

open import Agda.Primitive renaming (Set to Type; SSet to Typeᵉ) public

infixl 40 _∙_  _∘_
infix  35 _＝_
infixr 35 _×_
infixr 30 _,_ Σ _⇒_ Π
infix 30 _↓
infixr 20 𝛌
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

coe→ : {A B : Type} (e : A ≡ B) → A → B
coe→ reflᵉ a = a

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

-- Making this a datatype rather than a postulate leads to immense
-- speedups, probably because the parameters A and B aren't carried
-- around with each instance of _,_.  It also enables more rewrites to
-- fire, because the beta-rules for fst and snd don't have to match
-- the (nonexistent) parameters on _,_.  This choice does prevent us
-- from having an η-rule, since η-contraction violates the linearity
-- restriction in parameters, but at the moment that seems a small
-- price to pay.  (We can't make it a record, since then rewrite rules
-- like ap-fst wouldn't be allowed.)
data Σ (A : Type) (B : A → Type) : Type where
  _,_ : (a : A) → B a → Σ A B
syntax Σ A (λ x → B) = （ x ⦂ A ）× B
fst : {A : Type} {B : A → Type} → Σ A B → A
fst (a , _) = a

snd : {A : Type} {B : A → Type} (u : Σ A B) → B (fst u)
snd (_ , b) = b

--  Ση : (A : Type) (B : A → Type) (u : Σ A B) → (fst u , snd u) ≡ u
-- {-# REWRITE Ση #-}

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

_⇒_ : Type → Type → Type
A ⇒ B = （ x ⦂ A ）⇒ B

_∘_ : {A B C : Type} (g : B ⇒ C) (f : A ⇒ B) → (A ⇒ C)
g ∘ f = ƛ x ⇒ g ∙ (f ∙ x)

idmap : (A : Type) → (A ⇒ A)
idmap A = ƛ x ⇒ x

------------------------------
-- Dependent identity types
------------------------------

postulate
  Id : {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B a₀) (b₁ : B a₁) → Type
  Id-const : (A B : Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    Id {A} (λ _ → B) a₂ ≡ _＝_ {B}
  -- This should follow from the definitions in concrete cases.
  Id-refl : {A : Type} (B : A → Type) {a : A} →
    Id B (refl a) ≡ _＝_ {B a}
{-# REWRITE Id-const Id-refl #-}

postulate
  ap : {A : Type} {B : A → Type} (f : (x : A) → B x)
    {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → Id B a₂ (f a₀) (f a₁)
  ap-const : {A B : Type} (b : B) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    ap {A} (λ _ → b) a₂ ≡ refl b
  ap-idmap : {A : Type} {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    ap {A} (λ x → x) a₂ ≡ a₂
  -- This should also follow from the definitions in concrete cases.
  ap-refl : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) →
    ap f (refl a) ≡ refl (f a)
{-# REWRITE ap-const ap-idmap ap-refl #-}

-- These will be defined later as no-ops.
postulate
  →Id-ap : {A A' : Type} (f : A → A') (B : A' → Type)
    {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B (f a₀)) (b₁ : B (f a₁)) →
    Id (λ x → B (f x)) a₂ b₀ b₁ → Id B (ap f a₂) b₀ b₁
  ←Id-ap : {A A' : Type} (f : A → A') (B : A' → Type)
    {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B (f a₀)) (b₁ : B (f a₁)) →
    Id B (ap f a₂) b₀ b₁ → Id (λ x → B (f x)) a₂ b₀ b₁

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

--------------------------------------------------
-- Identifications, refl, and ap in Π-types
--------------------------------------------------

ID : Type → Type
ID A = （ a₀ ⦂ A ）× （ a₁ ⦂ A ）× a₀ ＝ a₁

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

IDᵈ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) → Type
IDᵈ A {δ₀} {δ₁} δ₂ = （ a₀ ⦂ A δ₀ ）× （ a₁ ⦂ A δ₁ ）× Id A δ₂ a₀ a₁

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

------------------------------
-- Amazing right adjoints
------------------------------

module _ {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type} where
  postulate
    √ : I → Type
    dig : {i₀ i₁ : I} {i₂ : i₀ ＝ i₁}
      {s₀ : √ i₀} {s₁ : √ i₁} (s₂ : Id √ i₂ s₀ s₁) →
      A i₀ i₁ i₂
    bury : {@♭ K : Type} (@♭ j : K → I)
      (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂)) →
      (k : K) → √ (j k)
{-
    dig-bury : {@♭ K : Type} (@♭ j : K → I)
      (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂))
      (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) →
      -- Requires Id-ap
      dig {ap j k₂} {bury j d k₀} {bury j d k₁} {!ap (bury j d) k₂!} ≡ d k₀ k₁ k₂
    Id-√ : {i₀ i₁ : I} {i₂ : i₀ ＝ i₁} (s₀ : √ A i₀) (s₁ : √ A i₁) →
      Id (𝛌 (√ A)) i₂ s₀ s₁ ≡
      A i₀ i₁ i₂ ×
      √ {（ i₀ ⦂ I ）× （ i₁ ⦂ I ）× （ i₂ ⦂ i₀ ＝ i₁ ）× √ A i₀ × √ A i₁}
        (λ u₀ u₁ u₂ → Id {（ i₀ ⦂ I ）× （ i₁ ⦂ I ）× (i₀ ＝ i₁)}
                       (ƛ iₓ ⇒ A (fst iₓ) (fst (snd iₓ)) (snd (snd iₓ)))
                       {fst u₀ , fst u₁ , fst u₂}
                       {fst (snd u₀) , fst (snd u₁) , ←Id-const I I (fst u₂) _ _ (fst (snd u₂))}
                       (fst (snd (snd u₀)) , →Id-const I I (fst (snd (snd u₀))) _ _ (fst (snd (snd u₁))) , {!!} )
                       (dig {I} {A} {fst u₀} {fst u₁} {fst u₂}
                         {fst (snd (snd (snd u₀)))} {fst (snd (snd (snd u₁)))} {!fst (snd (snd (snd u₂)))!} )
                       (dig {I} {A} {fst (snd u₀)} {fst (snd u₁)} {←Id-const I I (fst u₂) _ _ (fst (snd u₂))}
                         {snd (snd (snd (snd u₀)))} {snd (snd (snd (snd u₁)))} {!snd (snd (snd (snd u₂)))!}))
                       (i₀ , i₁ , i₂ , s₀ , s₁)
  {-# REWRITE Id-√ #-}
  postulate
    dig-def : {i₀ i₁ : I} (i₂ : i₀ ＝ i₁)
      {s₀ : √ A i₀} {s₁ : √ A i₁} (s₂ : Id (𝛌 (√ A)) i₂ s₀ s₁) →
      dig {A} {i₂} {s₀} {s₁} s₂ ≡ fst s₂
  {-# REWRITE dig-def #-}
-}

------------------------------
-- The universe
------------------------------

-- Morally, the definition of bitotal correspondence should be
{-
（ tr⇒ ⦂ A ⇒ B ）× （ tr⇐ ⦂ B ⇒ A ）× （ rel ⦂ A ⇒ B ⇒ Type ）×
  (（ x ⦂ A ）⇒ rel ∙ x ∙ (tr⇒ ∙ x)) × ( （ y ⦂ B ）⇒ rel ∙ (tr⇐ ∙ y) ∙ y)
-}
-- However, nested Σ-types seem to make Agda really slow, possibly
-- because our Σ-types are postulates and so all the parameters have
-- to be carried around as implicit arguments to fst, snd, and _,_.
-- Thus, instead we define bitotal correspondences to be a record.

-- As a mnemonic, whenever a coercion- or transport-like operation
-- belongs to a ⇒, so that it has to be applied with ∙, we name it
-- with a ⇒ or a ⇐.

record _≊_ (A B : Type) : Type where
  constructor ≊[_,_,_,_,_]
  field
    _／_～_ : A → B → Type
    coe⇒ : A ⇒ B
    coe⇐ : B ⇒ A
    push⇒ : （ a ⦂ A ）⇒ _／_～_ a (coe⇒ ∙ a)
    push⇐ : （ b ⦂ B ）⇒ _／_～_ (coe⇐ ∙ b) b
open _≊_

-- This means that the rules for computing ＝, Id, tr⇒, etc. in
-- Σ-types don't apply to _≊_, so for the theory to be complete, we'll
-- need to give separate rules for it.  Perhaps we can compute those
-- to the nested Σ-type that they would have been if it were a nested
-- Σ-type.  Or, if we'll need to actually use them in practice, maybe
-- we should make them a record too, and only go to Σ-types at the
-- next level.

postulate
  kan : (X : Type) → √ {Type} {λ X₀ X₁ X₂ → X₀ ≊ X₁} X

_↓ : {X₀ X₁ : Type} (X₂ : X₀ ＝ X₁) → X₀ ≊ X₁
_↓ {X₀} {X₁} X₂ = dig {Type} {λ X₀ X₁ X₂ → X₀ ≊ X₁} {X₀} {X₁} {X₂} {kan X₀} {kan X₁} (ap kan {X₀} {X₁} X₂)

------------------------------
-- Transport
------------------------------

-- The correspondence component of ((ap B e) ↓) is (Id B e), while the
-- other four components are transport and lifting.  We choose to
-- compute the former to the latter, so that transport and lifting
-- are, like Id, primitives (which, like Id, compute on type-formers).

module _ {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) where
  postulate
    tr⇒ : B a₀ ⇒ B a₁
    tr⇐ : B a₁ ⇒ B a₀
    lift⇒ : （ b₀ ⦂ B a₀ ）⇒ Id B a₂ b₀ (tr⇒ ∙ b₀)
    lift⇐ : （ b₁ ⦂ B a₁ ）⇒ Id B a₂ (tr⇐ ∙ b₁) b₁
    ap↓ : -- ap B a₂ ↓ ≡
      dig {Type} {λ X₀ X₁ X₂ → X₀ ≊ X₁} {B a₀} {B a₁} {ap B a₂} {kan (B a₀)} {kan (B a₁)} (ap kan (ap B a₂)) ≡
      ≊[ Id B a₂ , tr⇒ , tr⇐  , lift⇒ , lift⇐ ]
{-# REWRITE ap↓ #-}

-- Similarly, the correspondence part of ((refl A) ↓) is (_＝_ {A}),
-- while the other four components are trivial nudges.  We compute
-- these in the same direction.

module _ {A : Type} where
  postulate
    nudge⇒ : A ⇒ A
    nudge⇐ : A ⇒ A
    touch⇒ : （ a ⦂ A ）⇒ a ＝ nudge⇒ ∙ a
    touch⇐ : （ a ⦂ A ）⇒ nudge⇐ ∙ a ＝ a
    refl↓ : -- refl A ↓ ≡
      dig {Type} {λ X₀ X₁ X₂ → X₀ ≊ X₁} {A} {A} {refl A} {kan A} {kan A} (ap kan (refl A)) ≡
      ≊[ _＝_ {A} , nudge⇒ , nudge⇐ , touch⇒ , touch⇐ ]
{-# REWRITE refl↓ #-}

-- In fact, ap↓ and refl↓ should be lifted to all ap's.  That is,
-- something like (ap _↓ (ap (ap B e))) should compute to things like
-- (ap tr⇒), and so on.  Since ap-dig is comprehensible in terms of
-- √-types, this probably boils down to specifying that the ap's of
-- kan compute on ap's.  Maybe we can say that kan (and all its ap's)
-- belong to a class of terms on which ap-functoriality computes
-- backwards, so that (ap kan (ap (ap B e))) would compute to (ap (kan
-- (ap B e))) so that then the previous rule for (kan (ap B e)) could
-- fire?  I'm not sure how that would interact with dig.

----------------------------------------
-- Rules for transport
----------------------------------------

-- Because of the direction we compute, we need to give explicit
-- analogues for Id, ＝, transport, and nudging of all the rules for
-- ap and refl.

-- Analogues of ap-const (including Id-const)
module _ (A B : Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) where
  postulate
    tr⇒-const : (b₀ : B) → tr⇒ {A} (λ _ → B) a₂ ∙ b₀ ≡ nudge⇒ ∙ b₀
    tr⇐-const : (b₀ : B) → tr⇐ {A} (λ _ → B) a₂ ∙ b₀ ≡ nudge⇐ ∙ b₀
  {-# REWRITE tr⇒-const tr⇐-const #-}
  postulate
    lift⇒-const : (b₀ : B) → lift⇒ {A} (λ _ → B) a₂ ∙ b₀ ≡ touch⇒ ∙ b₀
    lift⇐-const : (b₀ : B) → lift⇐ {A} (λ _ → B) a₂ ∙ b₀ ≡ touch⇐ ∙ b₀
  {-# REWRITE lift⇒-const lift⇐-const #-}

-- Analogues of ap-refl (including Id-refl)
module _ {A : Type} (B : A → Type) (a : A) where
  postulate
    tr⇒-refl : (b₀ : B a) → tr⇒ B (refl a) ∙ b₀ ≡ nudge⇒ ∙ b₀
    tr⇐-refl : (b₀ : B a) → tr⇐ B (refl a) ∙ b₀ ≡ nudge⇐ ∙ b₀
  {-# REWRITE tr⇒-refl tr⇐-refl #-}
  postulate
    lift⇒-refl : (b₀ : B a) → lift⇒ B (refl a) ∙ b₀ ≡ touch⇒ ∙ b₀
    lift⇐-refl : (b₀ : B a) → lift⇐ B (refl a) ∙ b₀ ≡ touch⇐ ∙ b₀
  {-# REWRITE lift⇒-refl lift⇐-refl #-}

------------------------------------------------------------
-- Rules for identifications and transport on eliminators
------------------------------------------------------------

-- This also includes rules for the computation of ap on terms.  The
-- introduction forms of the universe are type-formers, and computing
-- all these things on them is what we're doing all throughout.  But
-- we also have to compute them on elimination forms of other types.

-- Analogues of refl-∙
postulate
  ＝-∙ : {A : Type} (f : A ⇒ Type) (a : A) (x₀ x₁ : f ∙ a) →
    (x₀ ＝ x₁) ≡ ((refl f ∙ (a , a , refl a) ↓) ／ x₀ ～ x₁)
  -- Note the directions of computation.
  --- refl (f ∙ a)             ⟼  refl f ∙ (a , a , refl a)                [by refl-∙]
  --- x₀ ~[ refl (f ∙ a) ] x₁  ⟼  (_＝_ {f ∙ a} x₀ x₁)                     [by refl↓]
  --- (_＝_ {f ∙ a} x₀ x₁)     ⟼  (x₀ ~[ refl f ∙ (a , a , refl a) ] x₁)   [by ＝-∙]
  -- Thus, ＝-∙ restores (some) confluence between refl-∙ and refl↓.
  nudge⇒-∙ : {A : Type} (f : A ⇒ Type) (a : A) →
    nudge⇒ ≡ coe⇒ (refl f ∙ (a , a , refl a) ↓)
  nudge⇐-∙ : {A : Type} (f : A ⇒ Type) (a : A) →
    nudge⇐ ≡ coe⇐ (refl f ∙ (a , a , refl a) ↓)
{-# REWRITE ＝-∙ nudge⇒-∙ nudge⇐-∙ #-}
postulate
  touch⇒-∙ : {A : Type} (f : A ⇒ Type) (a : A) →
    touch⇒ ≡ push⇒ (refl f ∙ (a , a , refl a) ↓)
  touch⇐-∙ : {A : Type} (f : A ⇒ Type) (a : A) →
    touch⇐ ≡ push⇐ (refl f ∙ (a , a , refl a) ↓)
{-# REWRITE touch⇒-∙ touch⇐-∙ #-}

-- Analogues of refl-fst
module _ {B : Type → Type} (u : Σ Type B) where
  postulate
    ＝-fst : (x₀ x₁ : fst u) → (x₀ ＝ x₁) ≡ (fst (refl u) ↓ ／ x₀ ～ x₁)
    nudge⇒-fst : nudge⇒ ≡ coe⇒ (fst (refl u) ↓)
    nudge⇐-fst : nudge⇐ ≡ coe⇐ (fst (refl u) ↓)
  {-# REWRITE ＝-fst nudge⇒-fst nudge⇐-fst #-}
  postulate
    touch⇒-fst : touch⇒ ≡ push⇒ (fst (refl u) ↓)
    touch⇐-fst : touch⇐ ≡ push⇐ (fst (refl u) ↓)
  {-# REWRITE touch⇒-fst touch⇐-fst #-}

-- Analogues of refl-snd
module _ {A : Type} (u : A × Type) where
  postulate
    ＝-snd : (x₀ x₁ : snd u) → (x₀ ＝ x₁) ≡ (snd (refl u) ↓ ／ x₀ ～ x₁)
    nudge⇒-snd : nudge⇒ ≡ coe⇒ (snd (refl u) ↓)
    nudge⇐-snd : nudge⇐ ≡ coe⇐ (snd (refl u) ↓)
  {-# REWRITE ＝-snd nudge⇒-snd nudge⇐-snd #-}
  postulate
    touch⇒-snd : touch⇒ ≡ push⇒ (snd (refl u) ↓)
    touch⇐-snd : touch⇐ ≡ push⇐ (snd (refl u) ↓)
  {-# REWRITE touch⇒-snd touch⇐-snd #-}

-- Analogues of ap-fst
module _  {Δ : Type} {B : Δ → Type → Type} (u : (δ : Δ) → Σ Type (B δ)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) where
  postulate
    Id-fst : (x₀ : fst (u δ₀)) (x₁ : fst (u δ₁)) →
      Id (λ δ → fst (u δ)) δ₂ x₀ x₁ ≡ (fst (ap u δ₂) ↓ ／ x₀ ～ x₁)
    tr⇒-fst : tr⇒ (λ δ → fst (u δ)) δ₂ ≡ coe⇒ (fst (ap u δ₂) ↓)
    tr⇐-fst : tr⇐ (λ δ → fst (u δ)) δ₂ ≡ coe⇐ (fst (ap u δ₂) ↓)
  {-# REWRITE Id-fst tr⇒-fst tr⇐-fst #-}
  postulate
    lift⇒-fst : lift⇒ (λ δ → fst (u δ)) δ₂ ≡ push⇒ (fst (ap u δ₂) ↓)
    lift⇐-fst : lift⇐ (λ δ → fst (u δ)) δ₂ ≡ push⇐ (fst (ap u δ₂) ↓)
  {-# REWRITE lift⇒-fst lift⇐-fst #-}

-- TODO: Analogues af ap-snd

-- Analogues of ap-∙
postulate
  Id-∙ : {Δ : Type} {A : Δ → Type} (f : (δ : Δ) → A δ ⇒ Type)
    (a : (δ : Δ) → A δ) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (x₀ : f δ₀ ∙ a δ₀) (x₁ : f δ₁ ∙ a δ₁) →
    Id (λ δ → f δ ∙ a δ) δ₂ x₀ x₁ ≡ (ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) ↓ ／ x₀ ～ x₁)
  tr⇒-∙ : {Δ : Type} {A : Δ → Type} (f : (δ : Δ) → A δ ⇒ Type)
    (a : (δ : Δ) → A δ) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    tr⇒ (λ δ → f δ ∙ a δ) δ₂ ≡ coe⇒ (ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) ↓)
  tr⇐-∙ : {Δ : Type} {A : Δ → Type} (f : (δ : Δ) → A δ ⇒ Type)
    (a : (δ : Δ) → A δ) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    tr⇐ (λ δ → f δ ∙ a δ) δ₂ ≡ coe⇐ (ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) ↓)
{-# REWRITE Id-∙ tr⇒-∙ tr⇐-∙ #-}
postulate
  lift⇒-∙ : {Δ : Type} {A : Δ → Type} (f : (δ : Δ) → A δ ⇒ Type)
    (a : (δ : Δ) → A δ) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    lift⇒ (λ δ → f δ ∙ a δ) δ₂ ≡ push⇒ (ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) ↓)
  lift⇐-∙ : {Δ : Type} {A : Δ → Type} (f : (δ : Δ) → A δ ⇒ Type)
    (a : (δ : Δ) → A δ) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    lift⇐ (λ δ → f δ ∙ a δ) δ₂ ≡ push⇐ (ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) ↓)
{-# REWRITE lift⇒-∙ lift⇐-∙ #-}


------------------------------
-- ap-snd and ap-, and ap-∙
------------------------------

-- Now that we have Id-∙ we can tackle these super-difficult aps.  The
-- problem with all of them is that their well-typedness seems to
-- depend on themselves.  However, we can convince Agda to accept them
-- if we build up in stages, first asserting simpler versions with
-- less type dependency.  We also have to interleave this process for
-- all three of them, since they depend on each other as well.

postulate
  ap-∙¹ : {Δ A B : Type}
    (f : (δ : Δ) → A ⇒ B) (a : (δ : Δ) → A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡ ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) 
  ap-snd¹ : {Δ A B : Type} (u : Δ → A × B) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ snd (ap u δ₂)
{-# REWRITE ap-∙¹ ap-snd¹ #-}

-- We also frequently use the following trick.  The rule Id-∙ only
-- fires on type families that belong to a ⇒ and are applied with ∙,
-- but for general rewriting we need these rules to apply to arbitrary
-- type families that belong to a →.  So we first define an element of
-- the type we need under the assumption of a ⇒ type family, and then
-- in the actual rewrite rule we hand off with a 𝛌-abstraction.

frob-ap-∙² : {Δ : Type} (A B : Δ ⇒ Type)
  (f : (δ : Δ) → (A ∙ δ) ⇒ (B ∙ δ)) (a : (δ : Δ) → A ∙ δ)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (B ∙_) δ₂ (f δ₀ ∙ a δ₀) (f δ₁ ∙ a δ₁)
frob-ap-∙² A B f a {δ₀} {δ₁} δ₂ = ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂)

postulate
  ap-∙² : {Δ : Type} {A B : Δ → Type}
    (f : (δ : Δ) → (A δ) ⇒ (B δ)) (a : (δ : Δ) → A δ)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡ frob-ap-∙² (𝛌 A) (𝛌 B) f a δ₂
{-# REWRITE ap-∙² #-}

frob-ap-snd² : {Δ : Type} (A B : Δ ⇒ Type) (u : (δ : Δ) → A ∙ δ × B ∙ δ)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (B ∙_) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd² A B u {δ₀} {δ₁} δ₂ = snd (ap u δ₂)

postulate
  ap-snd² : {Δ : Type} {A B : Δ → Type} (u : (δ : Δ) → A δ × B δ)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ frob-ap-snd² (𝛌 A) (𝛌 B) u δ₂
{-# REWRITE ap-snd² #-}

frob-ap-∙³ : {Δ A : Type} (B : A ⇒ Type)
  (f : (δ : Δ) → Π A (B ∙_)) (a : (δ : Δ) → A)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ (a z)) δ₂ (f δ₀ ∙ a δ₀) (f δ₁ ∙ a δ₁)
frob-ap-∙³ {Δ} {A} B f a {δ₀} {δ₁} δ₂ = ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂)

postulate
  ap-∙³ : {Δ A : Type} (B : A → Type)
    (f : (δ : Δ) → Π A B) (a : (δ : Δ) → A)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡ frob-ap-∙³ (𝛌 B) f a δ₂
{-# REWRITE ap-∙³ #-}

frob-ap-snd³ : {Δ A : Type} (B : A ⇒ Type)
  (u : (δ : Δ) → Σ A (B ∙_)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ (fst (u z))) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd³ B u δ₂ = snd (ap u δ₂)

postulate
  ap-snd³ : {Δ A : Type} (B : A → Type)
    (u : (δ : Δ) → Σ A B) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ frob-ap-snd³ (𝛌 B) u δ₂
{-# REWRITE ap-snd³ #-}

frob-ap-snd : {Δ : Type} (A : Δ ⇒ Type) (B : （ x ⦂ Δ ）⇒ A ∙ x ⇒ Type)
  (u : (δ : Δ) → Σ (A ∙ δ) (B ∙ δ ∙_)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ z ∙ (fst (u z))) δ₂ (snd (u δ₀)) (snd (u δ₁))
frob-ap-snd A B u δ₂ = snd (ap u δ₂)

postulate
  ap-snd : {Δ : Type} (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (u : (δ : Δ) → Σ (A δ) (B δ)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → snd (u δ)) δ₂ ≡ frob-ap-snd (𝛌 A) (ƛ δ ⇒ ƛ a ⇒ B δ a) u δ₂
{-# REWRITE ap-snd #-}

frob-ap-,³ : {Δ A : Type} (B : A ⇒ Type)
  (a : (x : Δ) → A) (b : (x : Δ) → B ∙ (a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id {Δ × A} (λ u → B ∙ (snd u)) {δ₀ , a δ₀} {δ₁ , a δ₁} (δ₂ , ap a δ₂) (b δ₀) (b δ₁)
frob-ap-,³ B a b δ₂ = ap b δ₂

postulate
  ap-,³ : {Δ A : Type} (B : A → Type)
    (a : (x : Δ) → A) (b : (x : Δ) → B (a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ x → (_,_ {A} {B} (a x) (b x))) δ₂ ≡ (ap a δ₂ , frob-ap-,³ (𝛌 B) a b δ₂)
{-# REWRITE ap-,³ #-}

frob-ap-, : {Δ : Type} (A : Δ ⇒ Type) (B : Σ Δ (A ∙_) ⇒ Type)
  (a : (x : Δ) → A ∙ x) (b : (x : Δ) → B ∙ (x , a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (B ∙_) (δ₂ , ap a δ₂) (b δ₀) (b δ₁)
frob-ap-, A B a b δ₂ = ap b δ₂

postulate
  ap-, : {Δ : Type} (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (a : (x : Δ) → A x) (b : (x : Δ) → B x (a x)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ x → (_,_ {A x} {B x} (a x) (b x))) δ₂ ≡ (ap a δ₂ , frob-ap-, (𝛌 A) (ƛ z ⇒ B (fst z) (snd z)) a b δ₂)
{-# REWRITE ap-, #-}

frob-ap-∙ : {Δ : Type} (A : Δ ⇒ Type) (B : Σ Δ (A ∙_) ⇒ Type)
  (f : (δ : Δ) → Π (A ∙ δ) (λ x → B ∙ (δ , x))) (a : (δ : Δ) → A ∙ δ)
  {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
  Id (λ z → B ∙ (z , a z)) δ₂ (f δ₀ ∙ a δ₀) (f δ₁ ∙ a δ₁)
frob-ap-∙ {Δ} A B f a {δ₀} {δ₁} δ₂ = ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) 

postulate
  ap-∙ : {Δ : Type} {A : Δ → Type} {B : (δ : Δ) → A δ → Type}
    (f : (δ : Δ) → Π (A δ) (B δ)) (a : (δ : Δ) → A δ)
    {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁) →
    ap (λ δ → f δ ∙ a δ) δ₂ ≡ frob-ap-∙ (𝛌 A) (ƛ z ⇒ B (fst z) (snd z)) f a δ₂
{-# REWRITE ap-∙ #-}

{-
----------------------------------------
-- Squares, filling, and symmetry
----------------------------------------

Sq : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
  (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) → Type
Sq A {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  Id {A × A} (λ u → fst u ＝ snd u) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) a₂₀ a₂₁

postulate
  sym : (A : Type) {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
    (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
    Sq A a₀₂ a₁₂ a₂₀ a₂₁ → Sq A a₂₀ a₂₁ a₀₂ a₁₂

-- We don't wrap composition and square-filling into ⇒ types, so we
-- name them with → and ← instead of ⇒ and ⇐.

comp→ : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) →
  a₀₁ ＝ a₁₁
comp→ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  tr⇒ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₀

fill→ : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) →
  Sq A a₀₂ a₁₂ a₂₀ (comp→ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀)
fill→ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ =
  lift⇒ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₀

comp← : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₁ : a₀₁ ＝ a₁₁) →
  a₀₀ ＝ a₁₀
comp← {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  tr⇐ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₁

fill← : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A a₀₂ a₁₂ (comp← {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁) a₂₁
fill← {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₁ =
  lift⇐ (λ aₓ → fst aₓ ＝ snd aₓ) {a₀₀ , a₁₀} {a₀₁ , a₁₁} (a₀₂ , a₁₂) ∙ a₂₁

comp↑ : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  a₁₀ ＝ a₁₁
comp↑ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ = comp→ {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₀₂

fill↑ : {A : Type} {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A a₀₂ (comp↑ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁) a₂₀ a₂₁
fill↑ {A} {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₂₀ a₂₁ =
  sym A {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₀₂ (comp→ {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₀₂)
    (fill→ {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₀₂) 

comp↓ : {A : Type} {a₀₀ a₀₁ : A} {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  a₀₀ ＝ a₀₁
comp↓ {A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ = comp← {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₁₂

fill↓ : {A : Type} {a₀₀ a₀₁ : A} {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁) (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq A (comp↓ {A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁) a₁₂ a₂₀ a₂₁
fill↓ {A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  sym A {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ (comp← {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₁₂) a₁₂
    (fill← {A} {a₀₀} {a₁₀} a₂₀ {a₀₁} {a₁₁} a₂₁ a₁₂)

------------------------------
-- Transport in ⊤
------------------------------

postulate
  nudge⇒-⊤ : (u : ⊤) → nudge⇒ ∙ u ≡ u
  nudge⇐-⊤ : (u : ⊤) → nudge⇐ ∙ u ≡ u
  touch⇒-⊤ : (u : ⊤) → touch⇒ ∙ u ≡ ★
  touch⇐-⊤ : (u : ⊤) → touch⇐ ∙ u ≡ ★
{-# REWRITE nudge⇒-⊤ nudge⇐-⊤ touch⇒-⊤ touch⇐-⊤ #-}

------------------------------
-- Transport in Σ-types
------------------------------

module _ (Δ : Type) (A : Δ → Type) (B : (x : Δ) → A x → Type) (δ₀ δ₁ : Δ) (δ₂ : δ₀ ＝ δ₁) where
  postulate
    tr⇒-Σ : (u₀ : Σ (A δ₀) (B δ₀)) →
      tr⇒ {Δ} (λ δ → Σ (A δ) (B δ)) δ₂ ∙ u₀ ≡
      (tr⇒ A δ₂ ∙ fst u₀ , tr⇒ (uncurry B) {δ₀ , fst u₀} {δ₁ , tr⇒ A δ₂ ∙ fst u₀} (δ₂ , lift⇒ A δ₂ ∙ fst u₀) ∙ snd u₀)
    tr⇐-Σ : (u₁ : Σ (A δ₁) (B δ₁)) →
      tr⇐ {Δ} (λ δ → Σ (A δ) (B δ)) δ₂ ∙ u₁ ≡
      (tr⇐ A δ₂ ∙ fst u₁ , tr⇐ (uncurry B) {δ₀ , tr⇐ A δ₂ ∙ fst u₁} {δ₁ , fst u₁} (δ₂ , lift⇐ A δ₂ ∙ fst u₁) ∙ snd u₁)
  {-# REWRITE tr⇒-Σ tr⇐-Σ #-}
  postulate
    lift⇒-Σ : (u₀ : Σ (A δ₀) (B δ₀)) →
      lift⇒ {Δ} (λ δ → Σ (A δ) (B δ)) δ₂ ∙ u₀ ≡
      (lift⇒ A δ₂ ∙ fst u₀ , lift⇒ (uncurry B) {δ₀ , fst u₀} {δ₁ , tr⇒ A δ₂ ∙ fst u₀} (δ₂ , lift⇒ A δ₂ ∙ fst u₀) ∙ snd u₀)
    lift⇐-Σ : (u₁ : Σ (A δ₁) (B δ₁)) →
      lift⇐ {Δ} (λ δ → Σ (A δ) (B δ)) δ₂ ∙ u₁ ≡
      (lift⇐ A δ₂ ∙ fst u₁ , lift⇐ (uncurry B) {δ₀ , tr⇐ A δ₂ ∙ fst u₁} {δ₁ , fst u₁} (δ₂ , lift⇐ A δ₂ ∙ fst u₁) ∙ snd u₁)
  {-# REWRITE lift⇒-Σ lift⇐-Σ #-}

module _ {A : Type} {B : A → Type} (u : Σ A B) where
  postulate
    nudge⇒-Σ : nudge⇒ ∙ u ≡ (nudge⇒ ∙ fst u , tr⇒ B (touch⇒ ∙ fst u) ∙ snd u)
    nudge⇐-Σ : nudge⇐ ∙ u ≡ (nudge⇐ ∙ fst u , tr⇐ B (touch⇐ ∙ fst u) ∙ snd u)
  {-# REWRITE nudge⇒-Σ nudge⇐-Σ #-}
  postulate
    touch⇒-Σ : touch⇒ ∙ u ≡ (touch⇒ ∙ fst u , lift⇒ B (touch⇒ ∙ fst u) ∙ snd u)
    touch⇐-Σ : touch⇐ ∙ u ≡ (touch⇐ ∙ fst u , lift⇐ B (touch⇐ ∙ fst u) ∙ snd u)
  {-# REWRITE touch⇒-Σ touch⇐-Σ #-}

------------------------------
-- Transport in Π-types
------------------------------

module _ (Δ : Type) (A : Δ → Type) (B : (x : Δ) → A x → Type) (δ₀ δ₁ : Δ) (δ₂ : δ₀ ＝ δ₁) where
  postulate
    tr⇒-Π : (f₀ : Π (A δ₀) (B δ₀)) (a₁ : A δ₁) →
      tr⇒ {Δ} (λ δ → Π (A δ) (B δ)) δ₂ ∙ f₀ ∙ a₁ ≡
      tr⇒ (uncurry B) {δ₀ , tr⇐ A δ₂ ∙ a₁} {δ₁ , a₁} (δ₂ , lift⇐ A δ₂ ∙ a₁)  ∙ (f₀ ∙ (tr⇐ A δ₂ ∙ a₁))
    tr⇐-Π : (f₁ : Π (A δ₁) (B δ₁)) (a₀ : A δ₀) →
      tr⇐ {Δ} (λ δ → Π (A δ) (B δ)) δ₂ ∙ f₁ ∙ a₀ ≡
      tr⇐ (uncurry B) {δ₀ , a₀} {δ₁ , tr⇒ A δ₂ ∙ a₀} (δ₂ , lift⇒ A δ₂ ∙ a₀)  ∙ (f₁ ∙ (tr⇒ A δ₂ ∙ a₀))
  {-# REWRITE tr⇒-Π tr⇐-Π #-}
  postulate
    lift⇒-Π : (f₀ : Π (A δ₀) (B δ₀)) (aₓ : IDᵈ A δ₂) →
      lift⇒ {Δ} (λ δ → Π (A δ) (B δ)) δ₂ ∙ f₀ ∙ aₓ ≡
      -- Requires dependent square-filling
      {!!}
    lift⇐-Π : (f₁ : Π (A δ₁) (B δ₁)) (aₓ : IDᵈ A δ₂) →
      lift⇐ {Δ} (λ δ → Π (A δ) (B δ)) δ₂ ∙ f₁ ∙ aₓ ≡
      {!!}
  --{-# REWRITE lift⇒-Π lift⇐-Π #-}

module _ {A : Type} {B : A → Type} (f : Π A B) where
  postulate
    nudge⇒-Π : (a : A) → nudge⇒ ∙ f ∙ a ≡ tr⇒ B (touch⇐ ∙ a) ∙ (f ∙ (nudge⇐ ∙ a))
    nudge⇐-Π : (a : A) → nudge⇐ ∙ f ∙ a ≡ tr⇐ B (touch⇒ ∙ a) ∙ (f ∙ (nudge⇒ ∙ a))
  {-# REWRITE nudge⇒-Π nudge⇐-Π #-}
  postulate
    touch⇒-Π : (aₓ : ID A) → touch⇒ ∙ f ∙ aₓ ≡ {!!}
    touch⇐-Π : (aₓ : ID A) → touch⇐ ∙ f ∙ aₓ ≡ {!!}
  --{-# REWRITE touch⇒-Π touch⇐-Π #-}

-}
