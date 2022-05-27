{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT where

open import Agda.Primitive renaming (Set to Type; SSet to Typeᵉ) public

------------------------------
-- Strict equality
------------------------------

data _≡_ {A : Typeᵉ} (a : A) : A → Typeᵉ where
  reflᵉ : a ≡ a

{-# BUILTIN REWRITE _≡_ #-}

_•_ : {A : Typeᵉ} {a b c : A} (p : a ≡ b) (q : b ≡ c) → a ≡ c
reflᵉ • reflᵉ = reflᵉ

rev : {A : Typeᵉ} {a b : A} (p : a ≡ b) → b ≡ a
rev reflᵉ = reflᵉ

cong : {A B : Typeᵉ} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
cong f reflᵉ = reflᵉ

cong2 : {A B C : Typeᵉ} (f : A → B → C) {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v) → f x u ≡ f y v
cong2 f reflᵉ reflᵉ = reflᵉ

cong3 : {A B C D : Typeᵉ} (f : A → B → C → D) {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v) {c d : C} (r : c ≡ d) → f x u c ≡ f y v d
cong3 f reflᵉ reflᵉ reflᵉ = reflᵉ

-- {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) (u : B x) → B y
coe→ : {A B : Type} → (A ≡ B) → A → B
coe→ reflᵉ u = u

-- {A : Type} (B : A → Type) {x y : A} (p : x ≡ y) (v : B y) → B x
-- Apparently we can't make A B : Typeᵉ here, even with cumulativity
coe← : {A B : Type} → (A ≡ B) → B → A
coe← reflᵉ v = v

coe←≡ : {A : Type} {e : A ≡ A} {a : A} → coe← e a ≡ a
coe←≡ {e = reflᵉ} = reflᵉ

axiomK : {A : Typeᵉ} {a : A} {p : a ≡ a} → p ≡ reflᵉ
axiomK {p = reflᵉ} = reflᵉ

uip : {A : Typeᵉ} {a b : A} {p q : a ≡ b} → p ≡ q
uip {q = reflᵉ} = axiomK

postulate
  funext : {A : Typeᵉ} {B : A → Typeᵉ} {f g : (x : A) → B x} (p : (x : A) → f x ≡ g x) → f ≡ g
  funext-reflᵉ : {A : Typeᵉ} {B : A → Typeᵉ} {f : (x : A) → B x} → funext {f = f} {g = f} (λ x → reflᵉ) ≡ reflᵉ

{-# REWRITE funext-reflᵉ #-}

------------------------------
-- Telescope exo-types
------------------------------

record ⊤ᵉ : Typeᵉ where
  constructor []

open ⊤ᵉ

-- We use two different kinds of Σ-exotypes, one defined as a record,
-- the other with postulates and rewrite rules.  Agda seems to have an
-- easier time pattern-matching against records to fill in implicit
-- arguments, so we use those where the user has to supply an element
-- of a telescope, and give them the nicer unprimed syntax.  But
-- record fields don't work as heads of a rewrite rule, so for the
-- bound arguments to Id and ap we use postulates instead.  The uglier
-- primed syntax is mainly used internally; the user is expected to
-- use pretty-printing MFun's to specify and view these arguments
-- containing binders.

-- Note that the type family must be fibrant-valued.
record Σᵉ (A : Typeᵉ) (B : A → Type) : Typeᵉ where
  constructor _∷_
  field
    pop : A
    top : B pop
open Σᵉ

eq-coe← : {A : Typeᵉ} {B : A → Type} {a₀ a₁ : A} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ ∷ coe← (cong B a₂) b₁) ≡ (a₁ ∷ b₁)
eq-coe← reflᵉ = reflᵉ

-- A telescope is a list of dependent types.  From it we can extract
-- an exotype of elements, using either kind of exo-sigma.

data Tel : Typeᵉ

-- The primed el is defined by mutual induction-recursion with the type Tel.
el′ : Tel → Typeᵉ

-- Its definition, in turn, involves the primed Σ-exotype.  But rather
-- than make this a generic Σ-exotype, we make its first argument a
-- Tel, with the second argument depending on the first via el′.  The
-- reason for this is explained below in the comments to ap-top.
-- Thus, it also has to be postulated mutually with Tel and el′.
postulate
  Σᵉ′ : (Δ : Tel) (B : el′ Δ → Type) → Typeᵉ

data Tel where
  ε : Tel
  _▸_ : (Δ : Tel) (A : el′ Δ → Type) → Tel

el′ ε = ⊤ᵉ
el′ (Δ ▸ A) = Σᵉ′ Δ A

-- Now we can give the constructors, destructors, and beta and eta rules for Σᵉ′.
postulate
  _∷′_ : {Δ : Tel} {B : el′ Δ → Type} (a : el′ Δ) (b : B a) → Σᵉ′ Δ B
  pop′ : {Δ : Tel} {B : el′ Δ → Type} (u : Σᵉ′ Δ B) → el′ Δ
  top′ : {Δ : Tel} {B : el′ Δ → Type} (u : Σᵉ′ Δ B) → B (pop′ u)
  βpop′ : {Δ : Tel} {B : el′ Δ → Type} (a : el′ Δ) (b : B a) → pop′ {B = B} (a ∷′ b) ≡ a
  η∷′ : {Δ : Tel} {B : el′ Δ → Type} (u : Σᵉ′ Δ B) → (pop′ u ∷′ top′ u) ≡ u

{-# REWRITE βpop′ η∷′ #-}

infixl 30 _▸_ _∷_ _∷′_

postulate
  βtop′ : {Δ : Tel} {B : el′ Δ → Type} (a : el′ Δ) (b : B a) → top′ {B = B} (a ∷′ b) ≡ b

{-# REWRITE βtop′ #-}

eq-coe←′ : {Δ : Tel} {B : el′ Δ → Type} {a₀ a₁ : el′ Δ} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ ∷′ coe← (cong B a₂) b₁) ≡ (a₁ ∷′ b₁)
eq-coe←′ reflᵉ = reflᵉ

-- The unprimed el is defined by mutual recursion with a coercion from unprimed to primed.
el : Tel → Typeᵉ

′ : {Δ : Tel} → el Δ → el′ Δ

el ε = ⊤ᵉ
el (Δ ▸ A) = Σᵉ (el Δ) (λ δ → A (′ δ))

′ {ε} x = x
′ {Δ ▸ A} (x ∷ y) = (′ x ∷′ y)

-- The coercion back the other direction is defined by mutual
-- recursion with a proof that it's a section.
` : {Δ : Tel} → el′ Δ → el Δ

′` : {Δ : Tel} (δ : el′ Δ) → ′ (` δ) ≡ δ

` {ε} x = x
` {Δ ▸ A} x = (` (pop′ x) ∷ coe← (cong A (′` _)) (top′ x))

′` {ε} δ = reflᵉ
′` {Δ ▸ A} δ = eq-coe←′ (′` _)

-- Finally, we can prove that it's a retraction too.
`′ : {Δ : Tel} (δ : el Δ) → ` (′ δ) ≡ δ
`′ {ε} δ = reflᵉ
`′ {Δ ▸ A} δ = (cong (λ y → (` (′ (pop δ)) ∷ coe← y (top δ))) uip • eq-coe← (`′ (pop δ)) {b₁ = top δ})

-- These coercions are strict inverses on canonical forms (tuples) for
-- concrete telescopes.  (This is verified in the testing section
-- below.)  Thus, we can consistently rewrite along them.
{-# REWRITE ′` `′ #-}

-- Amusingly, although we declare ′` and `′ as rewrites and so we
-- should never have to coerce along them from now on, we had to
-- coerce along ′` in the definition of `, and along `′ in the
-- definition of itself, before we were able to declare them as
-- rewrites.  Thus, those coercions may end up appearing in other
-- terms.  So we additionally postulate that these equalities
-- themselves are reflexivity, and declare *these* also as rewrites,
-- so that those coercions reduce away.
postulate
  ′`reflᵉ : {Δ : Tel} (δ : el′ Δ) → ′` δ ≡ reflᵉ
  `′reflᵉ : {Δ : Tel} (δ : el Δ) → `′ δ ≡ reflᵉ

{-# REWRITE ′`reflᵉ `′reflᵉ #-}

--------------------------------------------------
-- Identity types and identity telescopes
--------------------------------------------------

postulate
  -- Identity telescopes
  ID : (Δ : Tel) (δ₀ δ₁ : el Δ) → Tel
  -- Dependent/heterogeneous identity types
  Id′ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A (′ δ₀)) (a₁ : A (′ δ₁)) → Type
  -- Identity telescopes are built up from (dependent) identity types
  IDε : (δ₀ δ₁ : el ε) → ID ε δ₀ δ₁ ≡ ε
  ID▸ : (Δ : Tel) (A : el′ Δ → Type) (δ₀ δ₁ : el (Δ ▸ A)) →
    ID (Δ ▸ A) δ₀ δ₁ ≡ ID Δ (pop δ₀) (pop δ₁) ▸ λ δ₂ → Id′ A (` δ₂) (top δ₀) (top δ₁)
  -- Telescope ap
  ap : {Δ : Tel} {A : el′ Δ → Type} (f : (δ : el′ Δ) → A δ) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → Id′ A δ₂ (f (′ δ₀)) (f (′ δ₁))

{-# REWRITE IDε ID▸ #-}

-- Homogeneous identity types are heterogeneous over the empty telescope
Id : (A : Type) → A → A → Type
Id A a₀ a₁ = Id′ {Δ = ε} (λ _ → A) [] a₀ a₁

-- Reflexivity is nullary ap
refl : {A : Type} (a : A) → Id A a a
refl a = ap {Δ = ε} (λ _ → a) []

--------------------------------------------------
-- Identity types of constant families
--------------------------------------------------

postulate
  -- We assert this only for nonempty contexts.  Otherwise it would
  -- cause endless loops, since its output would also be a valid input.
  Id-const▸ : {Δ : Tel} (B : el′ Δ → Type) (A : Type) {δ₀ δ₁ : el (Δ ▸ B)} (δ₂ : el (ID (Δ ▸ B) δ₀ δ₁)) (a₀ a₁ : A) →
    Id′ {Δ = Δ ▸ B} (λ _ → A) δ₂ a₀ a₁ ≡ Id A a₀ a₁

{-# REWRITE Id-const▸  #-}

-- Since it holds by definition for the empty telescope and we've
-- asserted it for nonempty telescope, it is *true* for all telescope.
Id-const : (Δ : Tel) (A : Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ a₁ : A) → Id′ {Δ = Δ} (λ _ → A) δ₂ a₀ a₁ ≡ Id A a₀ a₁
Id-const ε A [] a₀ a₁ = reflᵉ
Id-const (Δ ▸ B) A δ₂ a₀ a₁ = Id-const▸ B A δ₂ a₀ a₁

-- However, I don't know how to make this hold definitionally for an
-- arbitrary telescope that hasn't yet been broken into empty/nonempty
-- cases.  This shouldn't be a problem for the *user*, who we intend
-- to only be using *concrete* telescopes which will always be either
-- empty or nonempty.  But it's an issue for stating further *general*
-- rules that are parametrized over an arbitrary telescope.  I can
-- think of two solutions:

-- 1. State all such rules in separate empty and nonempty versions.
-- This is more work, but will automatically behave correctly on all
-- concrete telescopes.

-- 2. State them by coercing along the general Id-const, above.  This
-- is easier, but to make the coercion vanish on concrete nonempty
-- telescopes we need the following rewrite rule.

Id-const▸-reflᵉ : {Δ : Tel} (B : el′ Δ → Type) (A : Type) {δ₀ δ₁ : el (Δ ▸ B)} (δ₂ : el (ID (Δ ▸ B) δ₀ δ₁)) (a₀ a₁ : A) →
  Id-const▸ B A δ₂ a₀ a₁ ≡ reflᵉ
Id-const▸-reflᵉ B A δ₂ a₀ a₁ = axiomK

{-# REWRITE Id-const▸-reflᵉ #-}

postulate
  -- For ap-const, we follow approach (1) above, and in fact we omit
  -- the case of the empty context since in that case it would be
  -- reducing refl to itself.
  ap-const▸ : {Δ : Tel} {X : el′ Δ → Type} {A : Type} (f : A) {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) →
    ap {Δ = Δ ▸ X} (λ _ → f) δ₂ ≡ refl f

{-# REWRITE ap-const▸ #-}

--------------------------------------------------
-- Identity types over reflexivity telescopes
--------------------------------------------------

-- We'd like to define reflexivity telescopes like this.  But that
-- isn't well-typed until we have Id-REFL, below; while Id-REFL
-- depends on REFL already existing.  So we instead make REFL a
-- postulate and give it the correct behavior with rewrite rules.

{-
REFL : {Δ : Tel} (δ : el Δ) → el (ID Δ δ δ)
REFL {ε} δ = []
REFL {Δ ▸ A} δ = REFL (pop δ) , {!refl (top δ)!}
-}

postulate
  REFL : {Δ : Tel} (δ : el Δ) → el (ID Δ δ δ)
  -- As with Id-const, we assert this only for nonempty contexts, to
  -- avoid endless loops, and follow it with similar boilerplate.
  Id-REFL▸ : {Δ : Tel} (B : el′ Δ → Type) (A : el′ (Δ ▸ B) → Type) (δ : el (Δ ▸ B)) (a₀ a₁ : A (′ δ)) →
    Id′ A (REFL δ) a₀ a₁ ≡ Id (A (′ δ)) a₀ a₁

{-# REWRITE Id-REFL▸ #-}

Id-REFL : {Δ : Tel} (A : el′ Δ → Type) (δ : el Δ) (a₀ a₁ : A (′ δ)) → Id′ A (REFL δ) a₀ a₁ ≡ Id (A (′ δ)) a₀ a₁
Id-REFL {Δ = ε} A δ a₀ a₁ = reflᵉ
Id-REFL {Δ = Δ ▸ B} A δ a₀ a₁ = Id-REFL▸ B A δ a₀ a₁

Id-REFL▸-reflᵉ : {Δ : Tel} (B : el′ Δ → Type) (A : el′ (Δ ▸ B) → Type) (δ : el (Δ ▸ B)) (a₀ a₁ : A (′ δ)) →
  Id-REFL▸ B A δ a₀ a₁ ≡ reflᵉ
Id-REFL▸-reflᵉ B A δ a₀ a₁ = axiomK

{-# REWRITE Id-REFL▸-reflᵉ #-}

postulate
  REFLε : (δ : el ε) → REFL {ε} δ ≡ []
  -- Here we have to coerce along Id-REFL to deal with an arbitrary
  -- context Δ (following approach (2) above).
  REFL▸ : (Δ : Tel) (A : el′ Δ → Type) (δ : el Δ) (a : A (′ δ)) →
    REFL {Δ ▸ A} (δ ∷ a) ≡ (REFL δ ∷ coe← (Id-REFL A δ a a) (refl a))
  -- We could alternatively state this rule separately in empty and
  -- nonempty versions (following approach (1) above).
  {-
  REFLε▸ : (A : el ε → Type) (δ : el ε) (a : A δ) →
    REFL {ε ▸ A} (δ ∷ a) ≡ (REFL δ ∷ refl a)
  REFL▸▸ : (Δ : Tel) (B : el′ Δ → Type) (A : el′ (Δ ▸ B) → Type) (δ : el (Δ ▸ B)) (a : A (′ δ)) →
    REFL {Δ ▸ B ▸ A} (δ ∷ a) ≡ (REFL δ ∷ refl a)
  -}

{-# REWRITE REFLε REFL▸ #-}

postulate
  ap-refl : {Δ : Tel} {A : el′ Δ → Type} (f : (δ : el′ Δ) → A δ) (δ : el Δ) →
    ap f (REFL δ) ≡ coe← (Id-REFL A δ (f (′ δ)) (f (′ δ))) (refl (f (′ δ)))

{-# REWRITE ap-refl #-}

-- However, it's unclear how useful this will ever be, since REFL
-- won't generally appear on its own, and can't be un-rewrited from
-- its decomposition into refls.

------------------------------
-- Ap on variables
------------------------------

-- The functoriality of ap on "identities" means that it acts as a
-- projection on variables.  However, these projections naturally lie
-- in identity types dependent on shorter telescopes, requiring
-- weakening to a longer telescope by functoriality.  Here's the
-- relevant kind of weakening-functoriality.

postulate
  Id-pop : {Δ : Tel} (X : el′ Δ → Type) (A : el′ Δ → Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) (a₀ : A (′ (pop δ₀))) (a₁ : A (′ (pop δ₁))) →
    Id′ (λ w → A (pop′ w)) δ₂ a₀ a₁ ≡ Id′ A (pop δ₂) a₀ a₁

-- Unfortunately, Id-pop is not a legal rewrite rule in either
-- direction, so we always have to coerce along it explicitly.  But we
-- can hope to make such coercions vanish on concrete telescopes and
-- types by giving rewrite rules for Id-pop that compute on A.  Here's
-- the first one, for constant families.

postulate
  Id-pop-const : {Δ : Tel} (X : el′ Δ → Type) (A : Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) (a₀ a₁ : A) →
    Id-pop X (λ _ → A) δ₂ a₀ a₁ ≡ rev (Id-const Δ A (pop δ₂) a₀ a₁)

-- {-# REWRITE Id-pop-const #-}

postulate
  -- Recall that variables in the telescope are represented as De
  -- Bruijn indices composed of top′ and pop′, with top′ on the
  -- outside.  To compute the correct projection from the
  -- identification argument of an ap on such a variable, we need to
  -- essentially reverse the order of these applications and put top′
  -- on the inside.  Thus we introduce an auxiliary function ap-var.
  ap-var : {Δ Θ : Tel} (A : el′ Θ → Type) (a : (w : el′ Θ) → A w)
    (ap-a : (w₀ w₁ : el Θ) (w₂ : el (ID Θ w₀ w₁)) → Id′ A w₂ (a (′ w₀)) (a (′ w₁)))
    (f : el′ Δ → el′ Θ) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    Id′ (λ w → A (f w)) δ₂ (a (f (′ δ₀))) (a (f (′ δ₁)))
  -- Now when computing, we detect a variable by the presence of top′
  -- and pass the computation off to ap-var.
  ap-top : {Δ Θ : Tel} (A : el′ Θ → Type) (f : el′ Δ → el′ (Θ ▸ A)) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ = Δ}                  -- Obviously a pattern binding Δ
    {A = λ w → A (pop′ (f w))}  -- "Any other term": doesn't bind anything
    (λ w → top′ {Θ} {A} (f w))     -- top′ and el′ are postulates, and (f w) is a pattern binding f, and Θ, A are bound patterns
    {δ₀} {δ₁} δ₂           -- All obviously patterns, binding δ₀ δ₁ δ₂
    ≡
    ap-var (λ w → A (pop′ w)) (λ w → top′ w) (λ w₀ w₁ w₂ → coe← (Id-pop A A w₂ (top w₀) (top w₁)) (top w₂)) f δ₂
  -- It's very subtle to have set things up so that the rule ap-top
  -- can fire as a rewrite.
  --
  -- For instance, if Σᵉ′ were a generic Σ-exotype (rather than taking
  -- a Tel as its first argument), then the LHS of ap-top only
  -- involves Θ inside el′.  But if Θ is concrete, then (el′ Θ)
  -- reduces to something involving Σᵉ′, preventing ap-top from
  -- matching against it.  If we try to fix this by asserting separate
  -- version of ap-top for ε and ▸, we seem to actually need a
  -- separate rule for each length of concrete context.
  --
  -- We could also try to get rid of Σᵉ′ completely and just use
  -- instances of el′ in defining the operations such as top′, pop′
  -- and "∷′".  Then el′ never reduces, so we can match against it.
  -- However, in this approach it seems impossible to give (el′ ε) an
  -- η-rule, since it isn't definitionally a record, and the η-rule
  -- for a unit type isn't rewritable.  This requires putting that
  -- η-rule explicitly in the definition of (′` ε δ), which causes it
  -- to appear coerced along in various places, and in particular
  -- prevents us from writing ([] ∷ a₂ ∷ b₂) without a coercion.
  --
  -- The current approach of having el′ compute to ⊤ᵉ or Σᵉ′, but with
  -- the first argument of Σᵉ′ being a Tel rather than an arbitrary
  -- exotype, so far seems to navigate between Scylla and Charybdis.
  --
  -- Finally, we give the recursive computation rules for ap-var.
  -- Note that although it's morally "defined by recursion", we have
  -- to implement this with postulates and rewrites because the
  -- recursion matches under a binder.
  ap-var-top : {Δ : Tel} (A : el′ Δ → Type) (a : (w : el′ Δ) → A w)
    (ap-a : (w₀ w₁ : el Δ) (w₂ : el (ID Δ w₀ w₁)) → Id′ A w₂ (a (′ w₀)) (a (′ w₁)))
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap-var A a ap-a (λ w → w) δ₂ ≡ ap-a δ₀ δ₁ δ₂
  ap-var-pop : {Δ Θ : Tel} (X : el′ Θ → Type) (A : el′ Θ → Type) (a : (w : el′ Θ) → A w)
    (ap-a : (w₀ w₁ : el Θ) (w₂ : el (ID Θ w₀ w₁)) → Id′ A w₂ (a (′ w₀)) (a (′ w₁)))
    (f : el′ Δ → el′ (Θ ▸ X)) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap-var A a ap-a (λ w → pop′ (f w)) δ₂ ≡
    ap-var (λ w → A (pop′ w)) (λ w → a (pop′ w))
      (λ w₀ w₁ w₂ → coe← (Id-pop X A w₂ (a (′ (pop w₀))) (a (′ (pop w₁)))) (ap-a (pop w₀) (pop w₁) (pop w₂))) f δ₂

{-# REWRITE ap-top ap-var-top ap-var-pop #-}

----------------------------------------
-- Functoriality of Id and Ap
----------------------------------------

-- This is a lot like Id-REFL, in fact the latter is morally a special
-- case of it.  But it may not be subject to the same infinite-loops
-- problem.

postulate
  AP : {Θ Δ : Tel} (f : el′ Θ → el′ Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → el (ID Δ (` (f (′ t₀))) (` (f (′ t₁))))
  -- This should really compute in the other direction.  (In actual
  -- HOTT, it is admissible over the structure of A.)  But Agda can't
  -- compute it in that direction.  In this direction, it sometimes
  -- rewrites, but not always, e.g. if the AP computes in a different
  -- way, so sometimes we may have to coerce along it explicitly.
  Id-AP : {Θ Δ : Tel} (f : el′ Θ → el′ Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (A : el′ Δ → Type) (a₀ : A (f (′ t₀))) (a₁ : A (f (′ t₁))) →
    Id′ A (AP f t₂) a₀ a₁ ≡ Id′ (λ w → A (f w)) t₂ a₀ a₁

{-# REWRITE Id-AP #-}

postulate
  APε : {Θ : Tel} (f : el′ Θ → el′ ε) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → AP f t₂ ≡ []
  AP▸ : {Θ Δ : Tel} (A : el′ Δ → Type) (f : el′ Θ → el′ (Δ ▸ A)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP {Θ} {Δ ▸ A} f t₂ ≡ (AP (λ w → pop′ (f w)) t₂ ∷ coe← (cong2 (Id′ (λ w → A (pop′ (f w))) t₂) coe←≡ coe←≡) (ap (λ w → top′ (f w)) t₂))

{-# REWRITE APε AP▸ #-}

postulate
  ap-AP : {Θ Δ : Tel} (f : el′ Θ → el′ Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {A : el′ Δ → Type} (g : (x : el′ Δ) → A x) →
    ap g (AP f t₂) ≡ ap (λ w → g (f w)) t₂

{-# REWRITE ap-AP #-}

-- Since this rule should always fire as a rewrite, we hopefully don't
-- need to prove it or explain how to compute with it.
postulate
  AP-idmap : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → AP {Δ} {Δ} (λ w → w) δ₂ ≡ δ₂ 
  -- Presumably we'll also want an AP-compose.

{-# REWRITE AP-idmap #-}

--------------------
-- Unit type
--------------------

record ⊤ : Type where
  constructor ★

postulate
  Id⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} {δ₂ : el (ID Δ δ₀ δ₁)} (u v : ⊤) → Id′ {Δ} (λ _ → ⊤) δ₂ u v ≡ ⊤

{-# REWRITE Id⊤ #-}

postulate
  ap★ : {Δ : Tel} {δ₀ δ₁ : el Δ} {δ₂ : el (ID Δ δ₀ δ₁)} → ap {Δ} (λ _ → ★) δ₂ ≡ ★
  -- I think Id-pop-⊤ should be a special case of Id-pop-const
  -- Id-pop-⊤ : {Δ : Tel} (X : el′ Δ → Type) {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) (a₀ a₁ : ⊤) →
  --   Id-pop X (λ _ → ⊤) δ₂ a₀ a₁ ≡ reflᵉ

{-# REWRITE ap★ #-}

--------------------
-- Product types
--------------------

-- Would it work to derive these from Σ-types?

postulate
  _×_ : Type → Type → Type
  _,_ : {A : Type} {B : Type} → A → B → A × B
  fst : {A : Type} {B : Type} → A × B → A
  snd : {A : Type} {B : Type} → A × B → B

infix 30 _×_

postulate
  βfst : (A : Type) (B : Type) (a : A) (b : B) → fst (a , b) ≡ a
  βsnd : (A : Type) (B : Type) (a : A) (b : B) → snd (a , b) ≡ b
  η, : (A : Type) (B : Type) (u : A × B) → (fst u , snd u) ≡ u
  Id× : {Δ : Tel} (A B : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u : A (′ δ₀) × B (′ δ₀)) (v : A (′ δ₁) × B (′ δ₁)) →
    Id′ (λ w → A w × B w) δ₂ u v ≡ Id′ A δ₂ (fst u) (fst v) × Id′ B δ₂ (snd u) (snd v)

{-# REWRITE βfst βsnd η, Id× #-}

postulate
  ap, : {Δ : Tel} (A B : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f : (x : el′ Δ) → A x) (g : (x : el′ Δ) → B x) →
    ap (λ x → (f x , g x)) δ₂ ≡ (ap f δ₂ , ap g δ₂)
  ap-fst : {Δ : Tel} (A B : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f : (x : el′ Δ) → A x × B x) →
    ap (λ x → fst (f x)) δ₂ ≡ fst (ap f δ₂)
  ap-snd : {Δ : Tel} (A B : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f : (x : el′ Δ) → A x × B x) →
    ap (λ x → snd (f x)) δ₂ ≡ snd (ap f δ₂)

{-# REWRITE ap, ap-fst ap-snd #-}

postulate
  Id-pop× : {Δ : Tel} (X : el′ Δ → Type) (A B : el′ Δ → Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁))
    (u₀ : A (′ (pop δ₀)) × B (′ (pop δ₀)) ) (u₁ : A (′ (pop δ₁)) × B  (′ (pop δ₁))) →
    Id-pop X (λ w → A w × B w) δ₂ u₀ u₁ ≡ cong2 _×_ (Id-pop X A δ₂ (fst u₀) (fst u₁)) (Id-pop X B δ₂ (snd u₀) (snd u₁))
  Id-AP× : {Θ Δ : Tel} (f : el′ Θ → el′ Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (A B : el′ Δ → Type) {u₀ : A (f (′ t₀)) × B (f (′ t₀))} {u₁ : A (f (′ t₁)) × B (f (′ t₁))} →
    -- Agda would accept reflᵉ as the RHS here, because Id-AP is a
    -- rewrite rule and it can fire here.  But I suspect that writing
    -- it explicitly with cong2 is better because it makes sense even
    -- if Id-AP can't be rewritten along in some case because we can't
    -- un-rewrite to get AP.
    Id-AP f t₂ (λ w → A w × B w) u₀ u₁ ≡ cong2 _×_ (Id-AP f t₂ A (fst u₀) (fst u₁)) (Id-AP f t₂ B (snd u₀) (snd u₁))

{-# REWRITE Id-pop× Id-AP× #-}

--------------------
-- Σ-types
--------------------

postulate
  Σ : (A : Type) → (B : A → Type) → Type
  _﹐_ : {A : Type} {B : A → Type} (a : A) → B a → Σ A B
  π₁ : {A : Type} {B : A → Type} → Σ A B → A
  π₂ : {A : Type} {B : A → Type} (u : Σ A B) → B (π₁ u)

postulate
  βπ₁ : (A : Type) (B : A → Type) (a : A) (b : B a) → π₁ {B = B} (a ﹐ b) ≡ a

{-# REWRITE βπ₁ #-}

postulate
  βπ₂ : (A : Type) (B : A → Type) (a : A) (b : B a) → π₂ {B = B} (a ﹐ b) ≡ b
  η﹐ : (A : Type) (B : A → Type) (u : Σ A B) → (π₁ u ﹐ π₂ u) ≡ u

{-# REWRITE βπ₂ η﹐ #-}

postulate
  IdΣ : {Δ : Tel} (A : el′ Δ → Type) (B : (w : el′ Δ) → A w → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₀ : Σ (A (′ δ₀)) (λ a → B (′ δ₀) a)) (u₁ : Σ (A (′ δ₁)) (λ a → B (′ δ₁) a)) →
      Id′ {Δ} (λ w → Σ (A w) (B w)) δ₂ u₀ u₁ ≡
       Σ (Id′ A δ₂ (π₁ u₀) (π₁ u₁)) (λ e → Id′ {Δ ▸ A} (λ w → B (pop′ w) (top′ w)) (δ₂ ∷ e) (π₂ u₀) (π₂ u₁))

{-# REWRITE IdΣ #-}

postulate
  ap﹐ : {Δ : Tel} {A : el′ Δ → Type} {B : (w : el′ Δ) → A w → Type} (f : (δ : el′ Δ) → A δ) (g : (δ : el′ Δ) → B δ (f δ))
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {A = λ w → Σ (A w) (B w)} (λ w → f w ﹐ g w) δ₂ ≡
    -- It's tempting to try
    --- (Id-pop A (λ w → B w (f w)) (δ₂ ∷ ap f δ₂) (g (′ δ₀)) (g (′ δ₁)))
    -- but weakening (λ w → B w (f w)) doesn't give B.  We have to
    -- substitute into the side that has the general form of B.
    (ap f δ₂ ﹐  coe← (Id-AP (λ w → (w ∷′ f w)) δ₂ (λ w → B (pop′ w) (top′ w)) _ _) (ap g δ₂))
  apπ₁ : {Δ : Tel} {A : el′ Δ → Type} {B : (w : el′ Δ) → A w → Type} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (u : (x : el′ Δ) → Σ (A x) (B x)) → ap (λ x → π₁ (u x)) δ₂ ≡ π₁ (ap u δ₂)

{-# REWRITE ap﹐ apπ₁ #-}

-- Here we have to coerce explicitly, because matching for a rewrite would require rewriting some argument backwards.
postulate
  apπ₂ : {Δ : Tel} {A : el′ Δ → Type} {B : (w : el′ Δ) → A w → Type} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (u : (x : el′ Δ) → Σ (A x) (B x)) →
    ap (λ x → π₂ (u x)) δ₂ ≡ coe→ (Id-AP (λ w → w ∷′ π₁ (u w)) δ₂ (λ w → B (pop′ w) (top′ w)) _ _) (π₂ (ap u δ₂))

{-# REWRITE apπ₂ #-}

{-
postulate
  Id-popΣ : {Δ : Tel} (X : el′ Δ → Type) (A : el′ Δ → Type) (B : (w : el′ Δ) → A w → Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁))
    (u₀ : Σ (A (′ (pop δ₀))) (λ a → B (′ (pop δ₀)) a)) (u₁ : Σ (A (′ (pop δ₁))) (λ a → B (′ (pop δ₁)) a)) →
    Id-pop X (λ w → Σ (A w) (B w)) δ₂ u₀ u₁ ≡
    -- Hmm... In addition to a dependent cong2, we need Id-pop for weakening B in the middle of the context.
    {! (Id-pop X A δ₂ (π₁ u₀) (π₁ u₁))  -- (Id-pop X B δ₂ (π₂ u₀) (π₂ u₁)) !}
-}

--------------------
-- Π-types
--------------------

postulate
  Π : (A : Type) (B : A → Type) → Type
  Λ : {A : Type} {B : A → Type} (f : (x : A) → B x) → Π A B
  _∙_ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → B a

infixl 30 _∙_

postulate
  β∙ : {A : Type} {B : A → Type} (f : (x : A) → B x) (a : A) → (Λ f ∙ a) ≡ f a
  ηΛ : {A : Type} {B : A → Type} (f : Π A B) → Λ (λ x → f ∙ x) ≡ f

{-# REWRITE β∙ ηΛ #-}

postulate
  IdΠ : {Δ : Tel} (A : el′ Δ → Type) (B : (w : el′ Δ) → A w → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (f₀ : Π (A (′ δ₀)) (λ a → B (′ δ₀) a)) (f₁ : Π (A (′ δ₁)) (λ a → B (′ δ₁) a)) →
    Id′ (λ w → Π (A w) (λ a → B w a)) δ₂ f₀ f₁ ≡
      Π (A (′ δ₀)) (λ a₀ →
      Π (A (′ δ₁)) (λ a₁ →
      Π (Id′ A δ₂ a₀ a₁) (λ a₂ →
        Id′ {Δ ▸ A} (λ w → B (pop′ w) (top′ w)) (δ₂ ∷ a₂) (f₀ ∙ a₀) (f₁ ∙ a₁))))

{-# REWRITE IdΠ #-}

postulate
  apΛ : {Δ : Tel} (A : el′ Δ → Type) (B : (w : el′ Δ) → A w → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (f : (x : el′ Δ) (a : A x) → B x a) →
    ap (λ x → Λ (f x)) δ₂ ≡ Λ λ a₀ → Λ λ a₁ → Λ λ a₂ → ap (λ w → f (pop′ w) (top′ w)) (δ₂ ∷ a₂) 
  ap∙ :  {Δ : Tel} (A : el′ Δ → Type) (B : (w : el′ Δ) → A w → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (f : (x : el′ Δ) → Π (A x) (B x)) (a : (x : el′ Δ) → A x) →
    ap (λ x → f x ∙ a x) δ₂ ≡
    coe→ (Id-AP (λ w → (w ∷′ a w)) δ₂ (λ w → B (pop′ w) (top′ w)) _ _) (ap f δ₂ ∙ (a (′ δ₀)) ∙ (a (′ δ₁)) ∙ (ap a δ₂)) 

{-# REWRITE apΛ ap∙ #-}

-- Id-popΠ will have the same problem as Id-popΣ.

------------------------------
-- Function types
------------------------------

_⟶_ : Type → Type → Type
A ⟶ B = Π A (λ _ → B)

infixr 20 _⟶_

--------------------------------------------------
-- Contractibility and 1-1 correspondences
--------------------------------------------------

isProp : (A : Type) → Type
isProp A = Π A (λ a₀ → Π A (λ a₁ → Id A a₀ a₁))

isContr : (A : Type) → Type
isContr A = A × isProp A

is11 : {A B : Type} (R : A ⟶ B ⟶ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⟶ B ⟶ Type) is11

postulate
  tr→ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A (′ δ₀)) → A (′ δ₁)
  lift→ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A (′ δ₀)) → Id′ A δ₂ a₀ (tr→ A δ₂ a₀)
  tr← : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A (′ δ₁)) → A (′ δ₀)
  lift← : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A (′ δ₁)) → Id′ A δ₂ (tr← A δ₂ a₁) a₁
  utr→ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A (′ δ₀))
    (a₁ a₁' : A (′ δ₁)) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') → Id (A (′ δ₁)) a₁ a₁'
  ulift→ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A (′ δ₀))
    (a₁ a₁' : A (′ δ₁)) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') →
    Id′ {ε ▸ (λ _ → A (′ δ₁))} (λ w → Id′ A δ₂ a₀ (top′ w)) ([] ∷ utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr← : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A (′ δ₁))
    (a₀ a₀' : A (′ δ₀)) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀' a₁) → Id (A (′ δ₀)) a₀ a₀'
  ulift← : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A (′ δ₁))
    (a₀ a₀' : A (′ δ₀)) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀' a₁) →
    Id′ {ε ▸ (λ _ → A (′ δ₀))} (λ w → Id′ A δ₂ (top′ w) a₁) ([] ∷ utr← A δ₂ a₁ a₀ a₀' a₂ a₂') a₂ a₂'

------------------------------
-- Copy-types
------------------------------

{-
infixl 30 _↑
infixl 30 _↓

postulate
  Copy : Type → Type
  _↑ : {A : Type} → A → Copy A
  _↓ : {A : Type} → Copy A → A
  ↑↓ : {A : Type} (a : A) → a ↑ ↓ ≡ a

{-# REWRITE ↑↓ #-}

postulate
  Id-Copy : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : Copy (A (′ δ₀))) (a₁ : Copy (A (′ δ₁))) →
    Id′ (λ w → Copy (A w)) δ₂ a₀ a₁ ≡ Copy (Id′ A δ₂ (a₀ ↓) (a₁ ↓))

{-# REWRITE Id-Copy #-}

postulate
  ap↑ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a : (w : el′ Δ) → A w) →
    ap (λ w → (a w) ↑) δ₂ ≡ (ap a δ₂) ↑
  ap↓ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a : (w : el′ Δ) → Copy (A w)) →
    ap (λ w → (a w) ↓) δ₂ ≡ (ap a δ₂) ↓

{-# REWRITE ap↑ ap↓ #-}

postulate
  Id-pop-Copy : {Δ : Tel} (X : el′ Δ → Type) (A : el′ Δ → Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁))
    (u₀ : Copy (A (′ (pop δ₀)))) (u₁ : Copy (A (′ (pop δ₁)))) →
    Id-pop X (λ w → Copy (A w)) δ₂ u₀ u₁ ≡ cong Copy (Id-pop X A δ₂ (u₀ ↓) (u₁ ↓))

{-# REWRITE Id-pop-Copy #-}
-}

------------------------------
-- The universe
------------------------------

-- With Copy-types, apU leads to an internal error.  So for now, we
-- just postulate one level of copy/uncopy.

-- postulate
--   IdU : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (A B : Type) →
--     Id′ {Δ} (λ _ → Type) δ₂ A B ≡ Copy (11Corr A B)

-- {-# REWRITE IdU #-}

postulate
  uncopy : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) {A B : Type} →
    Id′ {Δ} (λ _ → Type) δ₂ A B → 11Corr A B
  copy : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) {A B : Type} →
    11Corr A B → Id′ {Δ} (λ _ → Type) δ₂ A B
  uncopy-copy : (Δ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) {A B : Type} (E : 11Corr A B) →
    uncopy Δ δ₂ (copy Δ δ₂ E) ≡ E
  apU : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    uncopy Δ δ₂ (ap A δ₂) ≡
    ((Λ λ a₀ → Λ λ a₁ → Id′ A δ₂ a₀ a₁) ﹐ 
    ((Λ λ a₀ → (tr→ A δ₂ a₀ ﹐ lift→ A δ₂ a₀) ,
         Λ λ x → Λ λ x' → utr→ A δ₂ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift→ A δ₂ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ) ,
      Λ λ a₁ → (tr← A δ₂ a₁ ﹐ lift← A δ₂ a₁) ,
         Λ λ x → Λ λ x' → utr← A δ₂ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift← A δ₂ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ))

{-# REWRITE uncopy-copy apU #-}

----------------------------------------
-- Computing 1-1 correspondences
----------------------------------------

postulate
  tr→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤) → tr→ {Δ} (λ _ → ⊤) δ₂ a₀ ≡ a₀
  lift→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤) → lift→ {Δ} (λ _ → ⊤) δ₂ a₀ ≡ ★
  tr←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤) → tr← {Δ} (λ _ → ⊤) δ₂ a₁ ≡ a₁
  lift←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤) → lift← {Δ} (λ _ → ⊤) δ₂ a₁ ≡ ★
  utr→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤)
    (a₁ a₁' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁') →
    utr→ {Δ} (λ _ → ⊤) δ₂ a₀ a₁ a₁' a₂ a₂' ≡ ★
  ulift→⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : ⊤)
    (a₁ a₁' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁') →
    ulift→ {Δ} (λ _ → ⊤) δ₂ a₀ a₁ a₁' a₂ a₂' ≡ ★
  utr←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤)
    (a₀ a₀' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀' a₁) →
    utr← {Δ} (λ _ → ⊤) δ₂ a₁ a₀ a₀' a₂ a₂' ≡ ★
  ulift←⊤ : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : ⊤)
    (a₀ a₀' : ⊤) (a₂ : Id′ {Δ} (λ _ → ⊤) δ₂ a₀ a₁) (a₂' : Id′ {Δ} (λ _ → ⊤) δ₂ a₀' a₁) →
    ulift← {Δ} (λ _ → ⊤) δ₂ a₁ a₀ a₀' a₂ a₂' ≡ ★

{-# REWRITE tr→⊤ lift→⊤ tr←⊤ lift←⊤ utr→⊤ ulift→⊤ utr←⊤ ulift←⊤ #-}

postulate
  tr→× : {Δ : Tel} (A B : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₀ : A (′ δ₀) × B (′ δ₀)) →
    tr→ (λ w → A w × B w) δ₂ u₀ ≡ (tr→ A δ₂ (fst u₀) , tr→ B δ₂ (snd u₀))
  tr←× : {Δ : Tel} (A B : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₁ : A (′ δ₁) × B (′ δ₁)) →
    tr← (λ w → A w × B w) δ₂ u₁ ≡ (tr← A δ₂ (fst u₁) , tr← B δ₂ (snd u₁))

{-# REWRITE tr→× tr←× #-}

postulate
  lift→× : {Δ : Tel} (A B : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₀ : A (′ δ₀) × B (′ δ₀)) →
    lift→ (λ w → A w × B w) δ₂ u₀ ≡ (lift→ A δ₂ (fst u₀) , lift→ B δ₂ (snd u₀))
  lift←× : {Δ : Tel} (A B : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (u₁ : A (′ δ₁) × B (′ δ₁)) →
    lift← (λ w → A w × B w) δ₂ u₁ ≡ (lift← A δ₂ (fst u₁) , lift← B δ₂ (snd u₁))

{-# REWRITE lift→× lift←× #-}

  -- utr→ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A (′ δ₀))
  --   (a₁ a₁' : A (′ δ₁)) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') → Id (A (′ δ₁)) a₁ a₁'
  -- ulift→ : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A (′ δ₀))
  --   (a₁ a₁' : A (′ δ₁)) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') →
  --   Id′ {ε ▸ (λ _ → A (′ δ₁))} (λ w → Id′ A δ₂ a₀ (top′ w)) ([] ∷ utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  -- utr← : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A (′ δ₁))
  --   (a₀ a₀' : A (′ δ₀)) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀' a₁) → Id (A (′ δ₀)) a₀ a₀'
  -- ulift← : {Δ : Tel} (A : el′ Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A (′ δ₁))
  --   (a₀ a₀' : A (′ δ₀)) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀' a₁) →
  --   Id′ {ε ▸ (λ _ → A (′ δ₀))} (λ w → Id′ A δ₂ (top′ w) a₁) ([] ∷ utr← A δ₂ a₁ a₀ a₀' a₂ a₂') a₂ a₂'

-- ...

--------------------
-- Symmetry
--------------------

-- ...

----------------------------------------
-- Examples for testing
----------------------------------------

postulate
  A : Type
  a₀ a₁ : A
  a₂ : Id A a₀ a₁

A′ : el′ ε → Type
A′ _ = A

postulate
  B : el′ (ε ▸ A′) → Type
  b₀ : B ([] ∷′ a₀)
  b₁ : B ([] ∷′ a₁)
  b₂ : Id′ B ([] ∷ a₂) b₀ b₁
  C : el′ (ε ▸ A′ ▸ B) → Type
  c₀ : C ([] ∷′ a₀ ∷′ b₀)
  c₁ : C ([] ∷′ a₁ ∷′ b₁)
  c₂ : Id′ C ([] ∷ a₂ ∷ b₂) c₀ c₁

-- Testing that ` and ′ are definitional inverses on concrete telescopes.
`′test : `′ {ε ▸ A′ ▸ B ▸ C} ([] ∷ a₀ ∷ b₀ ∷ c₀) ≡ reflᵉ
`′test = reflᵉ

′`test : ′` {ε ▸ A′ ▸ B ▸ C} ([] ∷′ a₀ ∷′ b₀ ∷′ c₀) ≡ reflᵉ
′`test = reflᵉ

-- Testing normalization of ap-top (normalize these with C-c C-n).
-- Observe that the results involve coercions along Id-pop, but we can
-- hope that for concrete types these will compute away.  In
-- particular, with Id-pop-const, the coercions already vanish for the
-- "-A" versions.
egA-A = ap {Δ = ε ▸ A′} (λ w → top′ w) ([] ∷ a₂)
egAB-B = ap {Δ = ε ▸ A′ ▸ B} (λ w → top′ w) ([] ∷ a₂ ∷ b₂)
egAB-A = ap {Δ = ε ▸ A′ ▸ B} (λ w → top′ (pop′ w)) ([] ∷ a₂ ∷ b₂)
egABC-C = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top′ w) ([] ∷ a₂ ∷ b₂ ∷ c₂)
egABC-B = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top′ (pop′ w)) ([] ∷ a₂ ∷ b₂ ∷ c₂)
egABC-A = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top′ (pop′ (pop′ w))) ([] ∷ a₂ ∷ b₂ ∷ c₂)
