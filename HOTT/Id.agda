{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity #-}

module HOTT.Id where

open import HOTT.Rewrite
open import HOTT.Telescope

--------------------------------------------------
-- Identity types and identity telescopes
--------------------------------------------------

postulate
  -- Identity telescopes
  ID : (Δ : Tel) (δ₀ δ₁ : el Δ) → Tel
  -- Dependent/heterogeneous identity types
  Id′ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀) (a₁ : A δ₁) → Type
  -- Identity telescopes are built up from (dependent) identity types
  IDε : (δ₀ δ₁ : el ε) → ID ε δ₀ δ₁ ≡ ε
  ID▸ : (Δ : Tel) (A : el Δ → Type) (δ₀ δ₁ : el (Δ ▸ A)) →
    ID (Δ ▸ A) δ₀ δ₁ ≡ ID Δ (pop δ₀) (pop δ₁) ▸ λ δ₂ → Id′ A δ₂ (top δ₀) (top δ₁)
  -- Telescope ap
  ap : {Δ : Tel} {A : el Δ → Type} (f : (δ : el Δ) → A δ) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → Id′ A δ₂ (f δ₀) (f δ₁)

{-# REWRITE IDε ID▸ #-}

-- Homogeneous identity types are heterogeneous over the empty telescope
Id : (A : Type) → A → A → Type
Id A a₀ a₁ = Id′ {Δ = ε} (λ _ → A) [] a₀ a₁

-- Reflexivity is nullary ap
refl : {A : Type} (a : A) → Id A a a
refl a = ap {Δ = ε} (λ _ → a) []

-- Dependent identity *telescopes*!
postulate
  ID′ : {Δ : Tel} (Θ : el Δ → Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (t₀ : el (Θ δ₀)) (t₁ : el (Θ δ₁)) → Tel
  ID► : {Δ : Tel} (Θ : el Δ → Tel) (h₀ h₁ : el (Δ ► Θ)) →
    ID (Δ ► Θ) h₀ h₁ ≡ ID Δ (POP Θ h₀) (POP Θ h₁) ► λ w₂ → ID′ Θ w₂ (TOP Θ h₀) (TOP Θ h₁)

{-# REWRITE ID► #-}

postulate
  ID′ε : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (t₀ t₁ : el ε) → ID′ {Δ} (λ _ → ε) δ₂ t₀ t₁ ≡ ε
  ID′▸ : {Δ : Tel} (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (t₀ : el (Θ δ₀ ▸ A δ₀)) (t₁ : el (Θ δ₁ ▸ A δ₁)) →
    ID′ (λ w → Θ w ▸ A w) δ₂ t₀ t₁ ≡
    ID′ Θ δ₂ (pop t₀) (pop t₁) ▸
    (λ t₂ → Id′ {Δ ► Θ} (λ w → A (POP Θ w) (TOP Θ w))
            {PAIR Θ δ₀ (pop t₀)} {PAIR Θ δ₁ (pop t₁)}
            (PAIR (λ w → ID′ Θ w (pop t₀) (pop t₁)) δ₂ t₂)
            (top t₀) (top t₁))

{-# REWRITE ID′ε ID′▸ #-}

--------------------------------------------------
-- Identity types of constant families
--------------------------------------------------

postulate
  -- We assert this only for nonempty contexts.  Otherwise it would
  -- cause endless loops, since its output would also be a valid input.
  Id-const▸ : {Δ : Tel} (B : el Δ → Type) (A : Type) {δ₀ δ₁ : el (Δ ▸ B)} (δ₂ : el (ID (Δ ▸ B) δ₀ δ₁)) (a₀ a₁ : A) →
    Id′ {Δ = Δ ▸ B} (λ _ → A) {δ₀} {δ₁} δ₂ a₀ a₁ ≡ Id A a₀ a₁

{-# REWRITE Id-const▸  #-}

-- Since it holds by definition for the empty telescope and we've
-- asserted it for nonempty telescope, it is *true* for all telescope.
Id-const : (Δ : Tel) (A : Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ a₁ : A) → Id′ {Δ = Δ} (λ _ → A) δ₂ a₀ a₁ ≡ Id A a₀ a₁
Id-const ε A [] a₀ a₁ = reflᵉ
Id-const (Δ ▸ B) A {δ₀} {δ₁} δ₂ a₀ a₁ = Id-const▸ B A {δ₀} {δ₁} δ₂ a₀ a₁

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

Id-const▸-reflᵉ : {Δ : Tel} (B : el Δ → Type) (A : Type) {δ₀ δ₁ : el (Δ ▸ B)} (δ₂ : el (ID (Δ ▸ B) δ₀ δ₁)) (a₀ a₁ : A) →
  Id-const▸ B A {δ₀} {δ₁} δ₂ a₀ a₁ ≡ reflᵉ
Id-const▸-reflᵉ B A δ₂ a₀ a₁ = axiomK

{-# REWRITE Id-const▸-reflᵉ #-}

postulate
  -- For ap-const, we follow approach (1) above, and in fact we omit
  -- the case of the empty context since in that case it would be
  -- reducing refl to itself.
  ap-const▸ : {Δ : Tel} {X : el Δ → Type} {A : Type} (f : A) {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) →
    ap {Δ = Δ ▸ X} (λ _ → f) {δ₀} {δ₁} δ₂ ≡ refl f

{-# REWRITE ap-const▸ #-}

-- For dependent identity telescopes, I think we can just rewrite
-- without worrying about loops, since telescope ID is *not* defined
-- as a special case of dependent telescope ID′.
postulate
  ID-const : (Δ : Tel) (Θ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ a₁ : el Θ) →
    ID′ {Δ = Δ} (λ _ → Θ) δ₂ a₀ a₁ ≡ ID Θ a₀ a₁

{-# REWRITE ID-const #-}


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
  Id-REFL▸ : {Δ : Tel} (B : el Δ → Type) (A : el (Δ ▸ B) → Type) (δ : el (Δ ▸ B)) (a₀ a₁ : A δ) →
    Id′ A (REFL δ) a₀ a₁ ≡ Id (A δ) a₀ a₁

{-# REWRITE Id-REFL▸ #-}

Id-REFL : {Δ : Tel} (A : el Δ → Type) (δ : el Δ) (a₀ a₁ : A δ) → Id′ A (REFL δ) a₀ a₁ ≡ Id (A δ) a₀ a₁
Id-REFL {Δ = ε} A δ a₀ a₁ = reflᵉ
Id-REFL {Δ = Δ ▸ B} A δ a₀ a₁ = Id-REFL▸ B A δ a₀ a₁

Id-REFL▸-reflᵉ : {Δ : Tel} (B : el Δ → Type) (A : el (Δ ▸ B) → Type) (δ : el (Δ ▸ B)) (a₀ a₁ : A δ) →
  Id-REFL▸ B A δ a₀ a₁ ≡ reflᵉ
Id-REFL▸-reflᵉ B A δ a₀ a₁ = axiomK

{-# REWRITE Id-REFL▸-reflᵉ #-}

postulate
  REFLε : (δ : el ε) → REFL {ε} δ ≡ []
  -- Here we have to coerce along Id-REFL to deal with an arbitrary
  -- context Δ (following approach (2) above).
  REFL▸ : (Δ : Tel) (A : el Δ → Type) (δ : el Δ) (a : A δ) →
    REFL {Δ ▸ A} (δ ∷ a) ≡ (REFL δ ∷ coe← (Id-REFL A δ a a) (refl a))
  -- We could alternatively state this rule separately in empty and
  -- nonempty versions (following approach (1) above).
  {-
  REFLε▸ : (A : el ε → Type) (δ : el ε) (a : A δ) →
    REFL {ε ▸ A} (δ ∷ a) ≡ (REFL δ ∷ refl a)
  REFL▸▸ : (Δ : Tel) (B : el Δ → Type) (A : el (Δ ▸ B) → Type) (δ : el (Δ ▸ B)) (a : A δ) →
    REFL {Δ ▸ B ▸ A} (δ ∷ a) ≡ (REFL δ ∷ refl a)
  -}

{-# REWRITE REFLε REFL▸ #-}

postulate
  ap-REFL : {Δ : Tel} {A : el Δ → Type} (f : (δ : el Δ) → A δ) (δ : el Δ) →
    ap f (REFL δ) ≡ coe← (Id-REFL A δ (f δ) (f δ)) (refl (f δ))

{-# REWRITE ap-REFL #-}

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
  Id-pop : {Δ : Tel} (X : el Δ → Type) (A : el Δ → Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) (a₀ : A (pop δ₀)) (a₁ : A (pop δ₁)) →
    Id′ (λ w → A (pop w)) {δ₀} {δ₁} δ₂ a₀ a₁ ≡ Id′ A (pop δ₂) a₀ a₁

-- Unfortunately, Id-pop is not a legal rewrite rule in either
-- direction, so we always have to coerce along it explicitly.  But we
-- can hope to make such coercions vanish on concrete telescopes and
-- types by giving rewrite rules for Id-pop that compute on A.  Here's
-- the first one, for constant families.

postulate
  Id-pop-const : {Δ : Tel} (X : el Δ → Type) (A : Type)
    {δ₀ δ₁ : el (Δ ▸ X)} (δ₂ : el (ID (Δ ▸ X) δ₀ δ₁)) (a₀ a₁ : A) →
    Id-pop X (λ _ → A) {δ₀} {δ₁} δ₂ a₀ a₁ ≡ rev (Id-const Δ A {pop δ₀} {pop δ₁} (pop δ₂) a₀ a₁)

{-# REWRITE Id-pop-const #-}

postulate
  -- Recall that variables in the telescope are represented as De
  -- Bruijn indices composed of top and pop, with top on the
  -- outside.  To compute the correct projection from the
  -- identification argument of an ap on such a variable, we need to
  -- essentially reverse the order of these applications and put top
  -- on the inside.  Thus we introduce an auxiliary function ap-var.
  ap-var : {Δ Θ : Tel} (A : el Θ → Type) (a : (w : el Θ) → A w)
    (ap-a : (w₀ w₁ : el Θ) (w₂ : el (ID Θ w₀ w₁)) → Id′ A w₂ (a w₀) (a w₁))
    (f : el Δ → el Θ) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    Id′ (λ w → A (f w)) δ₂ (a (f δ₀)) (a (f δ₁))
  -- Now when computing, we detect a variable by the presence of top
  -- and pass the computation off to ap-var.
  ap-top : {Δ Θ : Tel} (A : el Θ → Type) (f : el Δ → el (Θ ▸ A)) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap {Δ = Δ}                  -- Obviously a pattern binding Δ
    {A = λ w → A (pop (f w))}  -- "Any other term": doesn't bind anything
    (λ w → top {Θ} {A} (f w))     -- top and el are postulates, and (f w) is a pattern binding f, and Θ, A are bound patterns
    {δ₀} {δ₁} δ₂           -- All obviously patterns, binding δ₀ δ₁ δ₂
    ≡
    ap-var (λ w → A (pop w)) (λ w → top w) (λ w₀ w₁ w₂ → coe← (Id-pop A A {w₀} {w₁} w₂ (top w₀) (top w₁)) (top w₂)) f δ₂
  -- It's very subtle to have set things up so that the rule ap-top
  -- can fire as a rewrite.
  --
  -- For instance, if Σᵉ were a generic Σ-exotype (rather than taking
  -- a Tel as its first argument), then the LHS of ap-top only
  -- involves Θ inside el.  But if Θ is concrete, then (el Θ)
  -- reduces to something involving Σᵉ, preventing ap-top from
  -- matching against it.  If we try to fix this by asserting separate
  -- version of ap-top for ε and ▸, we seem to actually need a
  -- separate rule for each length of concrete context.
  --
  -- We could also try to get rid of Σᵉ completely and just use
  -- instances of el as the types of the operations such as top, pop
  -- and ∷.  Then el never reduces, so we can match against it.
  -- However, in this approach it seems impossible to give (el ε) an
  -- η-rule, since it isn't definitionally a record, and the η-rule
  -- for a unit type isn't rewritable.
  --
  -- The current approach of having el compute to ⊤ᵉ or Σᵉ, but with
  -- the first argument of Σᵉ being a Tel rather than an arbitrary
  -- exotype, so far seems to navigate between Scylla and Charybdis.
  --
  -- Finally, we give the recursive computation rules for ap-var.
  -- Note that although it's morally "defined by recursion", we have
  -- to implement this with postulates and rewrites because the
  -- recursion matches under a binder.
  ap-var-top : {Δ : Tel} (A : el Δ → Type) (a : (w : el Δ) → A w)
    (ap-a : (w₀ w₁ : el Δ) (w₂ : el (ID Δ w₀ w₁)) → Id′ A w₂ (a w₀) (a w₁))
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap-var A a ap-a (λ w → w) δ₂ ≡ ap-a δ₀ δ₁ δ₂
  ap-var-pop : {Δ Θ : Tel} (X : el Θ → Type) (A : el Θ → Type) (a : (w : el Θ) → A w)
    (ap-a : (w₀ w₁ : el Θ) (w₂ : el (ID Θ w₀ w₁)) → Id′ A w₂ (a w₀) (a w₁))
    (f : el Δ → el (Θ ▸ X)) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    ap-var A a ap-a (λ w → pop (f w)) δ₂ ≡
    ap-var (λ w → A (pop w)) (λ w → a (pop w))
      (λ w₀ w₁ w₂ → coe← (Id-pop X A {w₀} {w₁} w₂ (a (pop w₀)) (a (pop w₁))) (ap-a (pop w₀) (pop w₁) (pop w₂))) f δ₂

{-# REWRITE ap-top ap-var-top ap-var-pop #-}

----------------------------------------
-- Functoriality of Id and Ap
----------------------------------------

-- This is a lot like Id-REFL, in fact the latter is morally a special
-- case of it.  But it may not be subject to the same infinite-loops
-- problem.

postulate
  AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → el (ID Δ (f t₀) (f t₁))
  Id-AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (A : el Δ → Type) (a₀ : A (f t₀)) (a₁ : A (f t₁)) →
    Id′ A (AP f t₂) a₀ a₁ ≡ Id′ (λ w → A (f w)) t₂ a₀ a₁

-- In actual HOTT, Id-AP is admissible over the structure of A.  Agda
-- can't compute it in that direction; in the other direction it
-- sometimes rewrites, but not always, e.g. if the AP computes in a
-- different way.  Unfortunately, if we declare it as a rewrite, then
-- when it fails to rewrite, we have trouble coercing along it
-- explicitly, since the rewrite happens eagerly and prevents the
-- types from matching.  So we decline to make it a rewrite at all,
-- and coerce all the time.  Hopefully we can make it compute away on
-- concrete types by giving clauses for them.
--- {-# REWRITE Id-AP #-}

postulate
  APε : {Θ : Tel} (f : el Θ → el ε) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → AP f t₂ ≡ []
  AP∷ : {Θ Δ : Tel} (A : el Δ → Type) (f : el Θ → el Δ) (a : (w : el Θ) → A (f w)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP {Θ} {Δ ▸ A} (λ w → (f w ∷ a w)) t₂ ≡
    (AP f t₂ ∷ coe← (Id-AP f t₂ A (a t₀) (a t₁)) (ap a t₂))
  AP-POP : {Γ : Tel} {Δ : Tel} (Θ : el Δ → Tel) (f : el Γ → el (Δ ► Θ)) (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP (λ w → POP Θ (f w)) γ₂ ≡
    POP (λ w₂ → ID′ Θ w₂ (TOP Θ (f γ₀)) (TOP Θ (f γ₁))) (AP f γ₂)
  AP-pop : {Γ : Tel} {Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) {γ₀ γ₁ : el Γ} (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP (λ w → pop (f w)) γ₂ ≡ pop (AP f γ₂)
  -- For a general AP-PAIR, we'd need a dependent AP′.  But we can do
  -- POP-AP-PAIR, and the constant version AP-PR, without it.
  POP-AP-PAIR : {Γ Δ : Tel} (Θ : el Δ → Tel) (f : el Γ → el Δ) (g : (w : el Γ) → el (Θ (f w)))
    {γ₀ γ₁ : el Γ} (γ₂ : el (ID Γ γ₀ γ₁)) →
    POP (λ w₂ → ID′ Θ w₂ (g γ₀) (g γ₁)) (AP (λ w → PAIR Θ (f w) (g w)) γ₂) ≡ AP f γ₂
  AP-PR : {Γ Δ Θ : Tel} (f : el Γ → el Δ) (g : el Γ → el Θ) {γ₀ γ₁ : el Γ} (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP (λ w → PAIR (λ _ → Θ) (f w) (g w)) γ₂ ≡ PR (ID Δ (f γ₀) (f γ₁)) (ID Θ (g γ₀) (g γ₁)) (AP f γ₂) (AP g γ₂)

{-# REWRITE APε AP∷ AP-POP AP-pop POP-AP-PAIR AP-PR #-}

-- POP-AP-PAIR doesn't always seem to fire as a rewrite, I don't know
-- why.  So we assert that it's reflexivity, so that coercions along
-- it may reduce away.
postulate
  POP-AP-PAIR-reflᵉ : {Γ Δ : Tel} (Θ : el Δ → Tel) (f : el Γ → el Δ) (g : (w : el Γ) → el (Θ (f w)))
    {γ₀ γ₁ : el Γ} (γ₂ : el (ID Γ γ₀ γ₁)) →
    POP-AP-PAIR Θ f g γ₂ ≡ reflᵉ

{-# REWRITE POP-AP-PAIR-reflᵉ #-}

-- I don't know what the type of general AP-TOP should be, and we
-- haven't needed it yet.  The constant version is easier.
postulate
  AP-TOP-const : {Γ Δ Θ : Tel} (f : el Γ → el (Δ ► (λ _ → Θ))) (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP (λ w → TOP (λ _ → Θ) (f w)) γ₂ ≡
    TOP (λ w₂ → ID Θ (TOP (λ _ → Θ) (f γ₀)) (TOP (λ _ → Θ) (f γ₁))) (AP f γ₂)

{-# REWRITE AP-TOP-const #-}

postulate
  ap-AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {A : el Δ → Type} (g : (x : el Δ) → A x) →
    ap g (AP f t₂) ≡ coe← (Id-AP f t₂ A (g (f t₀)) (g (f t₁))) (ap (λ w → g (f w)) t₂)

{-# REWRITE ap-AP #-}

-- Since this rule should always fire as a rewrite, we hopefully don't
-- need to prove it or explain how to compute with it.
postulate
  AP-idmap : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → AP {Δ} {Δ} (λ w → w) δ₂ ≡ δ₂ 
  -- Presumably we'll also want an AP-compose, which won't be rewritable.

{-# REWRITE AP-idmap #-}

postulate
  Id-AP-idmap : {Δ : Tel} {t₀ t₁ : el Δ} (t₂ : el (ID Δ t₀ t₁))
    (A : el Δ → Type) (a₀ : A t₀) (a₁ : A t₁) →
    Id-AP {Δ} {Δ} (λ w → w) t₂ A a₀ a₁ ≡ reflᵉ

{-# REWRITE Id-AP-idmap #-}

postulate
  Id-AP-pop : {Γ : Tel} {Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁))
    (B : el Δ → Type) (b₀ : B (pop (f γ₀))) (b₁ : B (pop (f γ₁))) →
    Id-AP {Γ} {Δ} (λ w → pop {Δ} {A} (f w)) {γ₀} {γ₁} γ₂ B b₀ b₁ ≡
    (rev (Id-pop A B {f γ₀} {f γ₁} (AP f γ₂) b₀ b₁) • Id-AP f γ₂ (λ w → B (pop w)) b₀ b₁)

{-# REWRITE Id-AP-pop #-}

------------------------------
-- Transport
------------------------------

postulate
  tr→ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀) → A δ₁
  lift→ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀) → Id′ A δ₂ a₀ (tr→ A δ₂ a₀)
  tr← : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A δ₁) → A δ₀
  lift← : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A δ₁) → Id′ A δ₂ (tr← A δ₂ a₁) a₁
  utr→ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀)
    (a₁ a₁' : A δ₁) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') → Id (A δ₁) a₁ a₁'
  ulift→ : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ : A δ₀)
    (a₁ a₁' : A δ₁) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀ a₁') →
    Id′ {ε ▸ (λ _ → A δ₁)} (λ w → Id′ A δ₂ a₀ (top w)) {[] ∷ a₁} {[] ∷ a₁'} ([] ∷ utr→ A δ₂ a₀ a₁ a₁' a₂ a₂') a₂ a₂'
  utr← : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A δ₁)
    (a₀ a₀' : A δ₀) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀' a₁) → Id (A δ₀) a₀ a₀'
  ulift← : {Δ : Tel} (A : el Δ → Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₁ : A δ₁)
    (a₀ a₀' : A δ₀) (a₂ : Id′ A δ₂ a₀ a₁) (a₂' : Id′ A δ₂ a₀' a₁) →
    Id′ {ε ▸ (λ _ → A δ₀)} (λ w → Id′ A δ₂ (top w) a₁) {[] ∷ a₀} {[] ∷ a₀'} ([] ∷ utr← A δ₂ a₁ a₀ a₀' a₂ a₂') a₂ a₂'
