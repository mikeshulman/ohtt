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

-- We use two different kinds of sigma exotypes, one defined as a
-- record, the other with postulates and rewrite rules.  Agda seems to
-- have an easier time pattern-matching against records to fill in
-- implicit arguments, so we use those where the user has to supply an
-- element of a telescope, and give them the nicer unprimed syntax.
-- But record fields don't work as heads of a rewrite rule, so for the
-- bound arguments to Id and ap we use postulates instead.  The uglier
-- primed syntax is mainly used internally; the user is expected to
-- use pretty-printing MFun's to specify and view these bound
-- arguments.

record Σᵉ (A : Typeᵉ) (B : A → Type) : Typeᵉ where
  constructor _,_
  field
    pop : A
    top : B pop
open Σᵉ

-- TODO: Try giving Σᵉ′ a Tel as its first argument, applying el′ on its second argument.
postulate
  Σᵉ′ : (A : Typeᵉ) (B : A → Type) → Typeᵉ
  _,′_ : {A : Typeᵉ} {B : A → Type} (a : A) (b : B a) → Σᵉ′ A B
  pop′ : {A : Typeᵉ} {B : A → Type} (u : Σᵉ′ A B) → A
  top′ : {A : Typeᵉ} {B : A → Type} (u : Σᵉ′ A B) → B (pop′ u)
  βpop′ : {A : Typeᵉ} {B : A → Type} (a : A) (b : B a) → pop′ {B = B} (a ,′ b) ≡ a
  η,′ : {A : Typeᵉ} {B : A → Type} (u : Σᵉ′ A B) → (pop′ u ,′ top′ u) ≡ u

{-# REWRITE βpop′ η,′ #-}

postulate
  βtop′ : {A : Typeᵉ} {B : A → Type} (a : A) (b : B a) → top′ {B = B} (a ,′ b) ≡ b

{-# REWRITE βtop′ #-}

eq-coe←′ : {A : Typeᵉ} {B : A → Type} {a₀ a₁ : A} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ ,′ coe← (cong B a₂) b₁) ≡ (a₁ ,′ b₁)
eq-coe←′ reflᵉ = reflᵉ

eq-coe← : {A : Typeᵉ} {B : A → Type} {a₀ a₁ : A} (a₂ : a₀ ≡ a₁) {b₁ : B a₁} →
  (a₀ , coe← (cong B a₂) b₁) ≡ (a₁ , b₁)
eq-coe← reflᵉ = reflᵉ

-- A telescope is a list of dependent types.  From it we can extract
-- an exotype of elements, using either kind of exo-sigma.

data Tel : Typeᵉ

-- The primed el is defined by mutual induction-recursion with the type Tel.
el′ : Tel → Typeᵉ

data Tel where
  ε : Tel
  _▸_ : (Δ : Tel) (A : el′ Δ → Type) → Tel

infixl 30 _▸_ _,_

el′ ε = ⊤ᵉ
el′ (Δ ▸ A) = Σᵉ′ (el′ Δ) A

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

′` : (Δ : Tel) (δ : el′ Δ) → ′ (` δ) ≡ δ

` {ε} x = x
` {Δ ▸ A} x = (` (pop′ x) , coe← (cong A (′` _ _)) (top′ x))

′` ε δ = reflᵉ
′` (Δ ▸ A) δ = eq-coe←′ (′` _ _)

-- Finally, we can prove that it's a retraction too.
`′ : (Δ : Tel) (δ : el Δ) → ` (′ δ) ≡ δ
`′ ε δ = reflᵉ
`′ (Δ ▸ A) δ = (cong (λ y → (` (′ (pop δ)) , coe← y (top δ))) uip • eq-coe← (`′ Δ (pop δ)) {b₁ = top δ})

-- Since these are strict inverses on canonical forms (tuples), we can
-- consistently rewrite along them.
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
  -- Here we coerce along Id-const to deal with an arbitrary context Δ
  -- (following approach (2) above).
  ap-const : {Δ : Tel} {A : Type} (f : A) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ = Δ} (λ _ → f) δ₂ ≡ coe← (Id-const Δ A δ₂ f f) (refl f) 

{-# REWRITE ap-const #-}

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
  Id-REFL▸ : {Δ : Tel} (B : el′ Δ → Type) (A : el′ (Δ ▸ B) → Type) (δ : el (Δ ▸ B)) (a₀ a₁ : A (′ δ)) → Id′ A (REFL δ) a₀ a₁ ≡ Id (A (′ δ)) a₀ a₁

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

----------------------------------------
-- Functoriality of Id and Ap
----------------------------------------

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
-- direction, so we have to coerce along it explicitly.

postulate
  ap-var : {Δ Θ : Tel} (A : el′ Θ → Type) (a : (w : el′ Θ) → A w)
    (ap-a : (w₀ w₁ : el Θ) (w₂ : el (ID Θ w₀ w₁)) → Id′ A w₂ (a (′ w₀)) (a (′ w₁)))
    (f : el′ Δ → el′ Θ) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    Id′ (λ w → A (f w)) δ₂ (a (f (′ δ₀))) (a (f (′ δ₁)))
  -- ap-top is not actually getting rewritten along.  The problem
  -- seems to be that when Θ is concrete, (el′ Θ) reduces to ⊤ᵉ or
  -- Σᵉ′, which can't then be matched against (el′ Θ) for the rewrite
  -- to fire.  See below, ap-top⊤ᵉ does work in the case when Θ = ε.
  ap-top : {Δ Θ : Tel} (A : el′ Θ → Type) (f : el′ Δ → el′ (Θ ▸ A)) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ = Δ}                  -- Obviously a pattern binding Δ
    {A = λ w → A (pop′ (f w))}  -- "Any other term": doesn't bind anything
    (λ w → top′ {el′ Θ} {A} (f w))     -- top′ and el′ are postulates, and (f w) is a pattern binding f, and Θ, A are bound patterns
    {δ₀} {δ₁} δ₂           -- All obviously patterns, binding δ₀ δ₁ δ₂
    ≡
    ap-var (λ w → A (pop′ w)) (λ w → top′ w) (λ w₀ w₁ w₂ → coe← (Id-pop A A w₂ (top w₀) (top w₁)) (top w₂)) f δ₂
  ap-top⊤ᵉ : {Δ : Tel} (A : ⊤ᵉ → Type) (f : el′ Δ → Σᵉ′ ⊤ᵉ A) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ = Δ} {A = λ w → A (pop′ (f w))} (λ w → top′ {⊤ᵉ} {A} (f w)) {δ₀} {δ₁} δ₂ ≡
    ap-var (λ w → A (pop′ w)) (λ w → top′ w) (λ w₀ w₁ w₂ → coe← (Id-pop A A w₂ (top w₀) (top w₁)) (top w₂)) f δ₂
  -- It's not enough to have ap-topΣᵉ too, since we still end up
  -- trying to match against (el′ Θ) inside Σᵉ′.  I think we would
  -- need a separate rewrite rule for each length of concrete context.
  ap-topΣᵉ : {Δ Θ : Tel} (X : el′ Θ → Type) (A : el′ (Θ ▸ X) → Type) (f : el′ Δ → el′ (Θ ▸ X ▸ A)) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ = Δ} {A = λ w → A (pop′ (f w))} (λ w → top′ {Σᵉ′ (el′ Θ) X} {A} (f w)) {δ₀} {δ₁} δ₂ ≡
    ap-var (λ w → A (pop′ w)) (λ w → top′ w) (λ w₀ w₁ w₂ → coe← (Id-pop A A w₂ (top w₀) (top w₁))
      (coe→ (cong (λ q → Id′ A (pop (pop w₂) , q) (top w₀) (top w₁)) coe←≡) (top w₂))) f δ₂
  -- Would it work to define a "function" (with rewrites) that
  -- reassembles a nested Σᵉ′ back into a Tel?  Or, perhaps better,
  -- could we define el′ as a postulate or recursive record rather
  -- than as something that reduces?
  ap-var-top : {Δ : Tel} (A : el′ Δ → Type) (a : (w : el′ Δ) → A w)
    (ap-a : (w₀ w₁ : el Δ) (w₂ : el (ID Δ w₀ w₁)) → Id′ A w₂ (a (′ w₀)) (a (′ w₁)))
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap-var A a ap-a (λ w → w) δ₂ ≡  ap-a δ₀ δ₁ δ₂
  ap-var-pop : {Δ Θ : Tel} (X : el′ Θ → Type) (A : el′ Θ → Type) (a : (w : el′ Θ) → A w)
    (ap-a : (w₀ w₁ : el Θ) (w₂ : el (ID Θ w₀ w₁)) → Id′ A w₂ (a (′ w₀)) (a (′ w₁)))
    (f : el′ Δ → el′ (Θ ▸ X)) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap-var A a ap-a (λ w → pop′ (f w)) δ₂ ≡
    ap-var (λ w → A (pop′ w)) (λ w → a (pop′ w))
      (λ w₀ w₁ w₂ → coe← (Id-pop X A w₂ (a (′ (pop w₀))) (a (′ (pop w₁)))) (ap-a (pop w₀) (pop w₁) (pop w₂))) f δ₂

{-# REWRITE ap-top ap-top⊤ᵉ ap-topΣᵉ ap-var-top ap-var-pop #-}

postulate
  A : el′ ε → Type
  a₀ a₁ : A []
  a₂ : Id (A []) a₀ a₁
  B : el′ (ε ▸ A) → Type
  b₀ : B ([] ,′ a₀)
  b₁ : B ([] ,′ a₁)
  b₂ : Id′ B ([] , a₂) b₀ b₁

eg = ap {Δ = ε ▸ A} {A = λ w → A (pop′ w)} (λ w → (top′ w)) ([] , a₂)
eg' = ap-top A (λ w → w) ([] , a₂)
eg₂ = ap {Δ = ε ▸ A ▸ B} {A = λ w → B (pop′ w)} (λ w → (top′ w)) ([] , a₂ , b₂)
eg₂' = ap-top B (λ w → w) ([] , a₂ , b₂)


{-

postulate
  -- This should really compute in the other direction.  (In actual HOTT, it is proven admissible over the structure of A.)  But Agda can't compute it in that direction.  In this direction, it sometimes rewrites, but not always, e.g. if the ap computes in a different way, so sometimes we may have to coerce along it explicitly.
  Id¹-ap : {Δ₁ Δ₂ : Type} (A : Δ₂ → Type) (f : Δ₁ → Δ₂) {δ δ' : Δ₁} (ρ : Id Δ₁ δ δ') (a : A (f δ)) (a' : A (f δ')) →
    Id¹ A (ap f ρ) a a' ≡ Id¹ (λ x → A (f x)) ρ a a'
  -- ap-ap

{-# REWRITE ap-const ap-refl ap-idmap #-}
{-# REWRITE Id¹-ap #-}

postulate
  -- Like Id¹-ap, this should really compute in the other direction
  Id²-ap¹ : {Δ₁ Δ₂ : Type} {Δ₃ : Δ₂ → Type} (A : (x : Δ₂) → Δ₃ x → Type)
            (f : Δ₁ → Δ₂) (g : (x : Δ₁) → Δ₃ (f x)) {δ δ' : Δ₁} (ρ : Id Δ₁ δ δ')
            (a : A (f δ) (g δ)) (a' : A (f δ') (g δ')) →
     Id² A (ap f ρ) (ap g ρ) a a' ≡ Id¹ (λ x → A (f x) (g x)) ρ a a' 
  -- We assert this special case of it separately, since Agda can't rewrite ρ backwards to "ap idmap ρ".
  Id²-ap¹-idmap : {Δ₁ : Type} {Δ₃ : Δ₁ → Type} (A : (x : Δ₁) → Δ₃ x → Type)
            (g : (x : Δ₁) → Δ₃ x) {δ δ' : Δ₁} (ρ : Id Δ₁ δ δ')
            (a : A δ (g δ)) (a' : A δ' (g δ')) →
     Id² A ρ (ap g ρ) a a' ≡ Id¹ (λ x → A x (g x)) ρ a a' 

{-# REWRITE Id²-ap¹ #-}
{-# REWRITE Id²-ap¹-idmap #-}


-- Unit type

record ⊤ : Type where
  constructor ★

postulate
  Id⊤ : (u v : ⊤) → Id ⊤ u v ≡ ⊤

{-# REWRITE Id⊤ #-}

postulate
  refl★ : refl ★ ≡ ★
  -- This is a special case of ap-const
  --ap★ : {Δ : Type} {δ δ' : Δ} (ρ : Id Δ δ δ') → ap {Δ = Δ} {A = λ _ → ⊤} (λ _ → ★) ρ ≡ ★

-- Product types

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

