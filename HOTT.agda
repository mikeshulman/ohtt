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
  constructor _,_
  field
    pop : A
    top : B pop
open Σᵉ

eq-coe← : {A : Typeᵉ} {B : A → Type} {a₀ a₁ : A} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ , coe← (cong B a₂) b₁) ≡ (a₁ , b₁)
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
  _,′_ : {Δ : Tel} {B : el′ Δ → Type} (a : el′ Δ) (b : B a) → Σᵉ′ Δ B
  pop′ : {Δ : Tel} {B : el′ Δ → Type} (u : Σᵉ′ Δ B) → el′ Δ
  top′ : {Δ : Tel} {B : el′ Δ → Type} (u : Σᵉ′ Δ B) → B (pop′ u)
  βpop′ : {Δ : Tel} {B : el′ Δ → Type} (a : el′ Δ) (b : B a) → pop′ {B = B} (a ,′ b) ≡ a
  η,′ : {Δ : Tel} {B : el′ Δ → Type} (u : Σᵉ′ Δ B) → (pop′ u ,′ top′ u) ≡ u

{-# REWRITE βpop′ η,′ #-}

infixl 30 _▸_ _,_ _,′_

postulate
  βtop′ : {Δ : Tel} {B : el′ Δ → Type} (a : el′ Δ) (b : B a) → top′ {B = B} (a ,′ b) ≡ b

{-# REWRITE βtop′ #-}

eq-coe←′ : {Δ : Tel} {B : el′ Δ → Type} {a₀ a₁ : el′ Δ} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ ,′ coe← (cong B a₂) b₁) ≡ (a₁ ,′ b₁)
eq-coe←′ reflᵉ = reflᵉ

-- The unprimed el is defined by mutual recursion with a coercion from unprimed to primed.
el : Tel → Typeᵉ

′ : {Δ : Tel} → el Δ → el′ Δ

el ε = ⊤ᵉ
el (Δ ▸ A) = Σᵉ (el Δ) (λ δ → A (′ δ))

′ {ε} x = x
′ {Δ ▸ A} (x , y) = (′ x ,′ y)

-- The coercion back the other direction is defined by mutual
-- recursion with a proof that it's a section.
` : {Δ : Tel} → el′ Δ → el Δ

′` : {Δ : Tel} (δ : el′ Δ) → ′ (` δ) ≡ δ

` {ε} x = x
` {Δ ▸ A} x = (` (pop′ x) , coe← (cong A (′` _)) (top′ x))

′` {ε} δ = reflᵉ
′` {Δ ▸ A} δ = eq-coe←′ (′` _)

-- Finally, we can prove that it's a retraction too.
`′ : {Δ : Tel} (δ : el Δ) → ` (′ δ) ≡ δ
`′ {ε} δ = reflᵉ
`′ {Δ ▸ A} δ = (cong (λ y → (` (′ (pop δ)) , coe← y (top δ))) uip • eq-coe← (`′ (pop δ)) {b₁ = top δ})

-- These coercions are strict inverses on canonical forms (tuples) for
-- concrete telescopes.  (This is verified in the testing section
-- below.)  Thus, we can consistently rewrite along them.
{-# REWRITE ′` `′ #-}

------------------------------
-- Variables
------------------------------

data Var : Tel → Type where
  v0 : {Δ : Tel} (A : el′ Δ → Type) → Var (Δ ▸ A)
  vs : {Δ : Tel} (A : el′ Δ → Type) → Var Δ → Var (Δ ▸ A)

var-type : {Δ : Tel} (δ : el′ Δ) (v : Var Δ) → Type
var-type δ (v0 {Δ} A) = A (pop′ δ)
var-type δ (vs {Δ} A v) = var-type (pop′ δ) v

postulate
  var : {Δ : Tel} (δ : el′ Δ) (v : Var Δ) → var-type δ v
  -- var δ (v0 A) = top′ δ
  var-v0 : {Δ : Tel} (A : el′ Δ → Type) (δ : el′ (Δ ▸ A)) → var δ (v0 A) ≡ top′ δ
  -- var δ (vs A v) = var (pop′ δ) v
  var-vs : {Δ : Tel} (A : el′ Δ → Type) (v : Var Δ) (δ : el′ (Δ ▸ A)) → var δ (vs A v) ≡ var (pop′ δ) v

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
    REFL {Δ ▸ A} (δ , a) ≡ (REFL δ , coe← (Id-REFL A δ a a) (refl a))
  -- We could alternatively state this rule separately in empty and
  -- nonempty versions (following approach (1) above).
  {-
  REFLε▸ : (A : el ε → Type) (δ : el ε) (a : A δ) →
    REFL {ε ▸ A} (δ , a) ≡ (REFL δ , refl a)
  REFL▸▸ : (Δ : Tel) (B : el′ Δ → Type) (A : el′ (Δ ▸ B) → Type) (δ : el (Δ ▸ B)) (a : A (′ δ)) →
    REFL {Δ ▸ B ▸ A} (δ , a) ≡ (REFL δ , refl a)
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
-- direction, so we have to coerce along it explicitly.  But we can
-- hope to make such coercions vanish on concrete telescopes and types
-- by giving rewrite rules for Id-pop that compute on A.  Here's the
-- first one, for constant families.

postulate
  Id-pop-const : {Δ : Tel} (X : el′ Δ → Type) (A : Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) (a₀ a₁ : A) →
    Id-pop X (λ _ → A) δ₂ a₀ a₁ ≡ rev (Id-const Δ A (pop δ₂) a₀ a₁)

{-# REWRITE Id-pop-const #-}

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
  -- and ",′".  Then el′ never reduces, so we can match against it.
  -- However, in this approach it seems impossible to give (el′ ε) an
  -- η-rule, since it isn't definitionally a record, and the η-rule
  -- for a unit type isn't rewritable.  This requires putting that
  -- η-rule explicitly in the definition of (′` ε δ), which causes it
  -- to appear coerced along in various places, and in particular
  -- prevents us from writing ([] , a₂ , b₂) without a coercion.
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
    AP {Θ} {Δ ▸ A} f t₂ ≡ (AP (λ w → pop′ (f w)) t₂ , coe← (cong2 (Id′ (λ w → A (pop′ (f w))) t₂) coe←≡ coe←≡) (ap (λ w → top′ (f w)) t₂))

{-# REWRITE APε AP▸ #-}

postulate
  ap-AP : {Θ Δ : Tel} (f : el′ Θ → el′ Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {A : el′ Δ → Type} (g : (x : el′ Δ) → A x) →
    ap g (AP f t₂) ≡ ap (λ w → g (f w)) t₂

{-# REWRITE ap-AP #-}

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

{-

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
  Id× : (A : Type) (B : Type) (u v : A × B) → Id (A × B) u v ≡ (Id A (fst u) (fst v) × Id B (snd u) (snd v))
  Id¹× : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A B : Δ → Type) (u : A δ × B δ) (v : A δ' × B δ') →
    Id¹ (λ x → A x × B x) ρ u v ≡ (Id¹ A ρ (fst u) (fst v) × Id¹ B ρ (snd u) (snd v))
  Id²× : {Δ₀ : Type} {Δ₁ : Δ₀ → Type} (A B : (x : Δ₀) → Δ₁ x → Type)
        {δ₀ δ₀' : Δ₀} (ρ₀ : Id Δ₀ δ₀ δ₀') {δ₁ : Δ₁ δ₀} {δ₁' : Δ₁ δ₀'} (ρ₁ : Id¹ Δ₁ ρ₀ δ₁ δ₁')
        (u : A δ₀ δ₁ × B δ₀ δ₁) (v : A δ₀' δ₁' × B δ₀' δ₁') →
        Id² (λ x y → A x y × B x y) ρ₀ ρ₁ u v ≡ Id² A ρ₀ ρ₁ (fst u) (fst v) × Id² B ρ₀ ρ₁ (snd u) (snd v)

{-# REWRITE βfst βsnd η, Id× Id¹× Id²× #-}

postulate
  refl, : (A : Type) (B : Type) (a : A) (b : B) → refl (a , b) ≡ (refl a , refl b)
  refl-fst : (A : Type) (B : Type) (u : A × B) → refl (fst u) ≡ fst (refl u)
  refl-snd : (A : Type) (B : Type) (u : A × B) → refl (snd u) ≡ snd (refl u)
  ap, : {Δ : Type} (A B : Δ → Type) {δ δ' : Δ} (ρ : Id Δ δ δ') (f : (x : Δ) → A x) (g : (x : Δ) → B x) →
    ap (λ x → (f x , g x)) ρ ≡ (ap f ρ , ap g ρ)
  ap-fst : {Δ : Type} (A B : Δ → Type) {δ δ' : Δ} (ρ : Id Δ δ δ') (f : (x : Δ) → A x × B x) →
    ap (λ x → fst (f x)) ρ ≡ fst (ap f ρ)
  ap-snd : {Δ : Type} (A B : Δ → Type) {δ δ' : Δ} (ρ : Id Δ δ δ') (f : (x : Δ) → A x × B x) →
    ap (λ x → snd (f x)) ρ ≡ snd (ap f ρ)

{-# REWRITE refl, refl-fst refl-snd ap, ap-fst ap-snd #-}

-- Σ-types

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
  IdΣ : (A : Type) (B : A → Type) (u v : Σ A B) → Id (Σ A B) u v ≡ Σ (Id A (π₁ u) (π₁ v)) (λ e → Id¹ B e (π₂ u) (π₂ v))

{-# REWRITE βπ₂ η﹐ IdΣ #-}

postulate
  Id¹Σ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (u : Σ (A δ) (B δ)) (v : Σ (A δ') (B δ')) →
    Id¹ (λ x → Σ (A x) (B x)) ρ u v ≡
    Σ (Id¹ A ρ (π₁ u) (π₁ v)) (λ e → Id² B ρ e (π₂ u) (π₂ v))

{-# REWRITE Id¹Σ #-}

postulate
  refl﹐ : (A : Type) (B : A → Type) (a : A) (b : B a) → refl (_﹐_ {B = B} a b) ≡ (refl a ﹐ refl {A = B a} b)
  reflπ₁ : (A : Type) (B : A → Type) (u : Σ A B) → refl (π₁ u) ≡ π₁ (refl u)
  ap﹐ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
           (u : (x : Δ) → A x) (v : (x : Δ) → B x (u x)) →
           ap {A = λ x → Σ (A x) (B x)} (λ x → (u x ﹐ v x)) ρ ≡ (ap u ρ ﹐ ap v ρ)
  apπ₁ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
           (u : (x : Δ) → Σ (A x) (B x)) → ap (λ x → π₁ (u x)) ρ ≡ π₁ (ap u ρ)

{-# REWRITE refl﹐ reflπ₁ ap﹐ apπ₁ #-}

-- In these two, we have to coerce explicitly, because matching for a rewrite would require rewriting some argument backwards.
postulate
  reflπ₂ : (A : Type) (B : A → Type) (u : Σ A B) → 
    refl (π₂ u) ≡ coe→ (λ X → X) (Id¹-ap B π₁ {δ = u} {δ' = u} (refl u) (π₂ u) (π₂ u)) (π₂ (refl u))  
  apπ₂ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (u : (x : Δ) → Σ (A x) (B x)) →
    ap (λ x → π₂ (u x)) ρ ≡ coe→ (λ X → X) (Id²-ap¹-idmap B (λ x → π₁ (u x)) ρ (π₂ (u δ)) (π₂ (u δ'))) (π₂ (ap u ρ))

{-# REWRITE reflπ₂ apπ₂ #-}

-- Π-types

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
  IdΠ : (A : Type) (B : A → Type) (f g : Π A B) →
    Id (Π A B) f g ≡ Π A (λ a₀ → Π A (λ a₁ → Π (Id A a₀ a₁) (λ a₂ → Id¹ B a₂ (f ∙ a₀) (g ∙ a₁))))

{-# REWRITE IdΠ #-}

postulate
  Id¹Π : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type) (f : Π (A δ) (B δ)) (g : Π (A δ') (B δ')) →
    Id¹ (λ x → Π (A x) (B x)) ρ f g ≡ Π (A δ) (λ a₀ → Π (A δ') (λ a₁ → Π (Id¹ A ρ a₀ a₁) (λ a₂ → Id² B ρ a₂ (f ∙ a₀) (g ∙ a₁))))

{-# REWRITE Id¹Π #-}

postulate
  reflΛ : {A : Type} {B : A → Type} (f : (x : A) → B x) → refl (Λ f) ≡ Λ (λ a₀ → Λ (λ a₁ → Λ (λ a₂ → ap f a₂)))
  refl∙ : {A : Type} {B : A → Type} (f : Π A B) (a : A) → refl (f ∙ a) ≡ refl f ∙ a ∙ a ∙ refl a
  apΛ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type) (f : (x : Δ) (a : A x) → B x a) →
    ap (λ x → Λ (f x)) ρ ≡ Λ λ a₀ → Λ λ a₁ → Λ λ a₂ → ap² f ρ a₂
  ap∙ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') (A : Δ → Type) (B : (x : Δ) → A x → Type)
    (f : (x : Δ) → Π (A x) (B x)) (a : (x : Δ) → A x) →
    ap (λ x → f x ∙ a x) ρ ≡ ap f ρ ∙ (a δ) ∙ (a δ') ∙ (ap a ρ)

{-# REWRITE reflΛ refl∙ apΛ ap∙ #-}

-- Function types

_⟶_ : Type → Type → Type
A ⟶ B = Π A (λ _ → B)

infixr 20 _⟶_

-- Contractibility and 1-1 correspondences

isProp : (A : Type) → Type
isProp A = Π A (λ a₀ → Π A (λ a₁ → Id A a₀ a₁))

isContr : (A : Type) → Type
isContr A = A × isProp A

is11 : {A B : Type} (R : A ⟶ B ⟶ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⟶ B ⟶ Type) is11

postulate
  tr⁰→ : {A : Type} (a₀ : A) → A
  lift⁰→ : {A : Type} (a₀ : A) → Id A a₀ (tr⁰→ a₀)
  tr⁰← : {A : Type} (a₁ : A) → A
  lift⁰← : {A : Type} (a₁ : A) → Id A (tr⁰← a₁) a₁
  utr⁰→ : {A : Type} (a₀ a₁ a₁' : A) (a₂ : Id A a₀ a₁) (a₂' : Id A a₀ a₁') → Id A a₁ a₁'
  ulift⁰→ : {A : Type} (a₀ a₁ a₁' : A) (a₂ : Id A a₀ a₁) (a₂' : Id A a₀ a₁') → Id¹ (λ a → Id A a₀ a) (utr⁰→ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr⁰← : {A : Type} (a₁ a₀ a₀' : A) (a₂ : Id A a₀ a₁) (a₂' : Id A a₀' a₁) → Id A a₀ a₀'
  ulift⁰← : {A : Type} (a₁ a₀ a₀' : A) (a₂ : Id A a₀ a₁) (a₂' : Id A a₀' a₁) → Id¹ (λ a → Id A a a₁) (utr⁰← a₁ a₀ a₀' a₂ a₂') a₂ a₂'

postulate
  tr→ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₀ : A δ₀) → A δ₁
  lift→ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₀ : A δ₀) → Id¹ A δ₂ a₀ (tr→ A δ₂ a₀)
  tr← : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₁ : A δ₁) → A δ₀
  lift← : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₁ : A δ₁) → Id¹ A δ₂ (tr← A δ₂ a₁) a₁
  utr→ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₀ : A δ₀)
    (a₁ a₁' : A δ₁) (a₂ : Id¹ A δ₂ a₀ a₁) (a₂' : Id¹ A δ₂ a₀ a₁') → Id (A δ₁) a₁ a₁'
  ulift→ : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₀ : A δ₀)
    (a₁ a₁' : A δ₁) (a₂ : Id¹ A δ₂ a₀ a₁) (a₂' : Id¹ A δ₂ a₀ a₁') → Id¹ (λ a → Id¹ A δ₂ a₀ a) (utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr← : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₁ : A δ₁)
    (a₀ a₀' : A δ₀) (a₂ : Id¹ A δ₂ a₀ a₁) (a₂' : Id¹ A δ₂ a₀' a₁) → Id (A δ₀) a₀ a₀'
  ulift← : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) (a₁ : A δ₁)
    (a₀ a₀' : A δ₀) (a₂ : Id¹ A δ₂ a₀ a₁) (a₂' : Id¹ A δ₂ a₀' a₁) → Id¹ (λ a → Id¹ A δ₂ a a₁) (utr← A δ₂ a₁ a₀ a₀' a₂ a₂') a₂ a₂'

-- The universe

infixl 30 _↑
infixl 30 _↓

postulate
  _↑ : {A B : Type} → 11Corr A B → Id Type A B
  _↓ : {A B : Type} → Id Type A B → 11Corr A B
  ↑↓ : {A B : Type} (e : 11Corr A B) → e ↑ ↓ ≡ e

{-# REWRITE ↑↓ #-}

postulate
  reflU : (A : Type) → (refl A) ↓ ≡
    ((Λ λ a₀ → Λ λ a₁ → Id A a₀ a₁) ﹐
    ((Λ λ a₀ → (tr⁰→ a₀ ﹐ lift⁰→ a₀) ,
        Λ λ x → Λ λ x' → utr⁰→ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift⁰→ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x')) ,
     (Λ λ a₁ → (tr⁰← a₁ ﹐ lift⁰← a₁) ,
        Λ λ x → Λ λ x' → utr⁰← a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift⁰← a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x'))))
  apU : {Δ : Type} (A : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : Id Δ δ₀ δ₁) → (ap A δ₂) ↓ ≡
    ((Λ λ a₀ → Λ λ a₁ → Id¹ A δ₂ a₀ a₁) ﹐
    ((Λ λ a₀ → (tr→ A δ₂ a₀ ﹐ lift→ A δ₂ a₀) ,
        Λ λ x → Λ λ x' → utr→ A δ₂ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift→ A δ₂ a₀ (π₁ x) (π₁ x') (π₂ x) (π₂ x')) ,
      Λ λ a₁ → (tr← A δ₂ a₁ ﹐ lift← A δ₂ a₁) ,
        Λ λ x → Λ λ x' → utr← A δ₂ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x') ﹐ ulift← A δ₂ a₁ (π₁ x) (π₁ x') (π₂ x) (π₂ x')))

{-# REWRITE reflU apU #-}

-- Computing 1-1 correspondences

-- ...

-- Symmetry

postulate
  sym : {A : Type} {a₀₀ a₀₁ : A} {a₀₂ : Id A a₀₀ a₀₁} {a₁₀ a₁₁ : A} {a₁₂ : Id A a₁₀ a₁₁} {a₂₀ : Id A a₀₀ a₁₀} {a₂₁ : Id A a₀₁ a₁₁} →
    Id² (λ x y → Id A x y) a₀₂ a₁₂ a₂₀ a₂₁ → Id² (λ x y → Id A x y) a₂₀ a₂₁ a₀₂ a₁₂
  sym-sym : {A : Type} {a₀₀ a₀₁ : A} {a₀₂ : Id A a₀₀ a₀₁} {a₁₀ a₁₁ : A} {a₁₂ : Id A a₁₀ a₁₁} {a₂₀ : Id A a₀₀ a₁₀} {a₂₁ : Id A a₀₁ a₁₁}
    (a₂₂ : Id² (λ x y → Id A x y) a₀₂ a₁₂ a₂₀ a₂₁) →
    -- I can't guess why Agda needs some implicit arguments supplied here, but these particular ones suffice but not fewer.
    sym {a₁₁ = a₁₁} {a₂₀ = a₀₂} {a₂₁ = a₁₂} (sym {a₁₀ = a₁₀} {a₂₀ = a₂₀} {a₂₁ = a₂₁} a₂₂) ≡ a₂₂

{-# REWRITE sym-sym #-}

postulate
  sym× : {A B : Type} {x₀₀ x₀₁ : A × B} {x₀₂ : Id (A × B) x₀₀ x₀₁} {x₁₀ x₁₁ : A × B} {x₁₂ : Id (A × B) x₁₀ x₁₁}
    {x₂₀ : Id (A × B) x₀₀ x₁₀} {x₂₁ : Id (A × B) x₀₁ x₁₁}
    (x₂₂ : Id² {Δ₀ = A × B} {Δ₁ = λ _ → A × B} (λ x y → Id (A × B) x y) {δ₀ = x₀₀} {δ₀' = x₀₁} x₀₂ {δ₁ = x₁₀} {δ₁' = x₁₁} x₁₂ x₂₀ x₂₁) →
    sym {a₀₀ = x₀₀} {a₀₁ = x₀₁} {a₀₂ = x₀₂} {a₁₀ = x₁₀} {a₁₁ = x₁₁} {a₁₂ = x₁₂} {a₂₀ = x₂₀} {a₂₁ = x₂₁} x₂₂ ≡
    {!fst x₂₂
    --sym {A = A} {a₀₀ = fst x₀₀} {a₀₁ = fst x₀₁} {a₀₂ = fst x₀₂} {a₁₀ = fst x₁₀} {a₁₁ = fst x₁₁} {a₁₂ = fst x₁₂} {a₂₀ = fst x₂₀} {a₂₁ = fst x₂₁} (fst x₂₂)
    --sym (snd x₂₂))!}
-}



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
  b₀ : B ([] ,′ a₀)
  b₁ : B ([] ,′ a₁)
  b₂ : Id′ B ([] , a₂) b₀ b₁
  C : el′ (ε ▸ A′ ▸ B) → Type
  c₀ : C ([] ,′ a₀ ,′ b₀)
  c₁ : C ([] ,′ a₁ ,′ b₁)
  c₂ : Id′ C ([] , a₂ , b₂) c₀ c₁

-- Testing that ` and ′ are definitional inverses on concrete telescopes.
`′test : `′ {ε ▸ A′ ▸ B ▸ C} ([] , a₀ , b₀ , c₀) ≡ reflᵉ
`′test = reflᵉ

′`test : ′` {ε ▸ A′ ▸ B ▸ C} ([] ,′ a₀ ,′ b₀ ,′ c₀) ≡ reflᵉ
′`test = reflᵉ

-- Testing normalization of ap-top (normalize these with C-c C-n).
-- Observe that the results involve coercions along Id-pop, but we can
-- hope that for concrete types these will compute away.  In
-- particular, with Id-pop-const, the coercions already vanish for the
-- "-A" versions.
egA-A = ap {Δ = ε ▸ A′} (λ w → top′ w) ([] , a₂)
egAB-B = ap {Δ = ε ▸ A′ ▸ B} (λ w → top′ w) ([] , a₂ , b₂)
egAB-A = ap {Δ = ε ▸ A′ ▸ B} (λ w → top′ (pop′ w)) ([] , a₂ , b₂)
egABC-C = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top′ w) ([] , a₂ , b₂ , c₂)
egABC-B = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top′ (pop′ w)) ([] , a₂ , b₂ , c₂)
egABC-A = ap {Δ = ε ▸ A′ ▸ B ▸ C} (λ w → top′ (pop′ (pop′ w))) ([] , a₂ , b₂ , c₂)
