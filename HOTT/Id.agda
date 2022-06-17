{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Id where

open import HOTT.Rewrite
open import HOTT.Telescope
open Σᵉ

--------------------------------------------------
-- Identity types and identity telescopes
--------------------------------------------------

-- Identity telescopes, collated and bundled.
ID : Tel → Tel

-- We define these mutually together with their projections to the
-- original telescope.
_₀ : {Δ : Tel} → el (ID Δ) → el Δ
_₁ : {Δ : Tel} → el (ID Δ) → el Δ
infix 40 _₀ _₁

-- They are also mutual with the (postulated) dependent identity
-- *types* that they are composed of.
postulate
  -- Note that these depend on an element of the bundled (ID Δ), which
  -- consists of two points of Δ and an identification between them.
  Id′ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀)) (a₁ : A (δ ₁)) → Type

ID ε = ε
ID (Δ ▸ A) = ID Δ ▸ (λ δ → A (δ ₀)) ▸ (λ δa → A ((pop δa)₁)) ▸ (λ δaa → Id′ A (pop (pop δaa)) (top (pop δaa)) (top δaa))

_₀ {ε} _ = []
_₀ {Δ ▸ A} (δ ∷ a₀ ∷ a₁ ∷ a₂) = δ ₀ ∷ a₀

_₁ {ε} _ = []
_₁ {Δ ▸ A} (δ ∷ a₀ ∷ a₁ ∷ a₂) = δ ₁ ∷ a₁

-- Congruence for dependent identity types
Id′≡ : {Δ : Tel} (A : el Δ → Type)
    {γ δ : el (ID Δ)} (e : γ ≡ δ)
    {a₀ : A (γ ₀)} {b₀ : A (δ ₀)} (e₀ : a₀ ≡ʰ b₀)
    {a₁ : A (γ ₁)} {b₁ : A (δ ₁)} (e₁ : a₁ ≡ʰ b₁) →
    Id′ A γ a₀ a₁ ≡ Id′ A δ b₀ b₁
Id′≡ _ reflᵉ reflʰ reflʰ = reflᵉ

-- And for elements of an identity telescope
ID∷≡ : {Δ : Tel} (A : el Δ → Type)
       {δ δ' : el (ID Δ)} (ϕ : δ ≡ δ')
       {a₀ : A (δ ₀)} {a₀' : A (δ' ₀)} (e₀ : a₀ ≡ʰ a₀')
       {a₁ : A (δ ₁)} {a₁' : A (δ' ₁)} (e₁ : a₁ ≡ʰ a₁')
       {a₂ : Id′ A δ a₀ a₁} {a₂' : Id′ A δ' a₀' a₁'} (e₂ : a₂ ≡ʰ a₂') →
       _≡_ {el (ID (Δ ▸ A))} (δ ∷ a₀ ∷ a₁ ∷ a₂) (δ' ∷ a₀' ∷ a₁' ∷ a₂')
ID∷≡ A reflᵉ reflʰ reflʰ reflʰ = reflᵉ

----------------------------------------
-- ap, AP, and functoriality of Id′
----------------------------------------

postulate
  -- Since Id will be definitionally a special case of Id′, we don't
  -- need separate and non-dependent versions of ap.  Note that like
  -- Id′, it depends on an element of the bundled (ID Δ).
  ap : {Δ : Tel} {A : el Δ → Type} (f : (δ : el Δ) → A δ) (δ : el (ID Δ)) → Id′ A δ (f (δ ₀)) (f (δ ₁))

-- Telescope AP.  I hope we can get away with only the non-dependent
-- version.  We'd like to *define* it by recursion on the target:
{-
AP {Δ = ε} f γ = []
AP {Δ = Δ ▸ A} f γ = AP (λ x → pop (f x)) γ ∷
                     coe← (cong A (AP₀ (λ x → pop (f x)) γ)) (top (f (γ ₀))) ∷
                     coe← (cong A (AP₁ (λ x → pop (f x)) γ)) (top (f (γ ₁))) ∷
                     coe→ (Id′-AP (λ x → pop (f x)) γ A (top (f (γ ₀))) (top (f (γ ₁)))) (ap (λ x → top (f x)) γ)
-}
-- However, in order to get ap to compute on variables, we need AP to
-- compute on pop, and if it also computed on arbitrary telescopes
-- that would produce infinite loops.  (You can see an AP-pop in the
-- above definition.)  So instead we "define" it to compute in this
-- way only when the *term* is also of the form ∷.  This requires
-- matching inside a λ, so it has to be done with rewrite rules.  Note
-- that this is a *syntactic* restriction, not a semantic one: since ∷
-- satisfies an eta-rule, the two definitions have the same semantics.
postulate
  AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → el (ID Δ)

-- We define AP mutually with proofs that its projections are the
-- action of the original f on the projections.  We don't need
-- computation rules for these on variables, so we can define them as
-- actual functions that compute only on the telescope Δ, rather than
-- postulates with rewrite rules that restrict computation to terms f
-- that involving ∷.
postulate
  AP₀ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → (AP f γ)₀ ≡ f (γ ₀)
  AP₁ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → (AP f γ)₁ ≡ f (γ ₁)

{-# REWRITE AP₀ AP₁ #-}

-- We also define AP mutually with postulated naturality for Id′.
-- This rule should be admissible, meaning we will give rewrite rules
-- making it hold definitionally on all concrete telescopes and terms.
-- Specifically, Id′-AP should compute on types, like Id′.
postulate
  Id′-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : el Δ → Type) (a₀ : A (f (γ ₀))) (a₁ : A (f (γ ₁))) →
    -- Does this go in the wrong direction?  It might make sense for
    -- coe→ along it to go in the same direction as the function f.
    Id′ (λ w → A (f w)) γ a₀ a₁ ≡ Id′ A (AP f γ) a₀ a₁

-- Note that in defining AP, we have to coerce along AP₀, AP₁ and
-- Id′-AP, explaining why we need a mutual definition.
postulate
  APε : {Γ : Tel} (f : el Γ → el ε) (γ : el (ID Γ)) → AP {Δ = ε} f γ ≡ []
  AP∷ : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el Δ) (A : el Δ → Type) (g : (x : el Γ) → A (f x)) →
    AP {Δ = Δ ▸ A} (λ x → f x ∷ g x) γ ≡
    AP f γ ∷ g (γ ₀) ∷ g (γ ₁) ∷ coe→ (Id′-AP f γ A (g (γ ₀)) (g (γ ₁))) (ap g γ)

{-# REWRITE APε AP∷ #-}

-- We need these because _₀ and _₁ were defined by decomposing their
-- identification argument, rather than as a λ-abstraction whose head
-- is ∷.  For some reason, doing the latter is very slow.  But we
-- still want (AP _₀ δ) to reduce *as if* _₀ and _₁ had been defined
-- that way.
postulate
  AP-₀ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (ID (Δ ▸ A))) (γ : el (ID Γ)) →
    AP (λ x → f x ₀) γ ≡
    AP (λ x → pop (pop (pop (f x))) ₀) γ
    ∷ top (pop (pop (f (γ ₀))))
    ∷ top (pop (pop (f (γ ₁))))
    ∷ coe→ (Id′-AP (λ x → pop (pop (pop (f x)))₀) γ A (top (pop (pop (f (γ ₀))))) (top (pop (pop (f (γ ₁)))))) (ap (λ x → top (pop (pop (f x)))) γ)
  AP-₁ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (ID (Δ ▸ A))) (γ : el (ID Γ)) →
    AP (λ x → f x ₁) γ ≡
    AP (λ x → pop (pop (pop (f x))) ₀) γ
    ∷ top (pop (pop (f (γ ₀))))
    ∷ top (pop (pop (f (γ ₁))))
    ∷ coe→ (Id′-AP (λ x → pop (pop (pop (f x)))₀) γ A (top (pop (pop (f (γ ₀))))) (top (pop (pop (f (γ ₁)))))) (ap (λ x → top (pop (pop (f x)))) γ)

{-# REWRITE AP-₀ AP-₁ #-}

-- Unfortunately, AP∷ is non-confluent with eta-contraction η∷.  In
-- the context of a variable (f : el Γ → el (Δ ▸ A)), the term
--- AP (λ x → pop (f x) ∷ top (f x)) γ
-- reduces by AP-∷ to a 3-fold ∷ as above, but also reduces by η∷ to
-- (AP f γ) which is then neutral.  As we will see below, this
-- non-confluence in turn actually breaks subject reduction.

-- However, I hope that none of this bad stuff can happen in the
-- intended object-language fragment, where elements of telescopes and
-- functions valued in telescopes are never hypothesized.  In this
-- fragment, any such f has to be built from the variable (x : el Γ)
-- along with ∷, top, and pop, and since AP will compute on all of
-- them, (AP f γ) is not neutral and should eventually reduce to the
-- same result.

-- A useful derived rule for combining the admissible equality Id′-AP
-- with an equality of base identifications and heterogeneous
-- equalities of the endpoints.
Id′-AP≡ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) {δ : el (ID Δ)} (e : δ ≡ AP f γ)
    (A : el Δ → Type) {a₀ : A (f (γ ₀))} {a₁ : A (f (γ ₁))} {b₀ : A (δ ₀)} {b₁ : A (δ ₁)}
    (e₀ : a₀ ≡ʰ b₀) (e₁ : a₁ ≡ʰ b₁) →
    Id′ (λ w → A (f w)) γ a₀ a₁ ≡ Id′ A δ b₀ b₁
Id′-AP≡ f γ reflᵉ A {a₀} {a₁} .{a₀} .{a₁} reflʰ reflʰ = Id′-AP f γ A a₀ a₁

------------------------------
-- Functoriality of ap and AP
------------------------------

-- Functoriality for ap should be admissible, like Id′-AP.  However,
-- like ap, it should compute on terms, not types.  We make this a
-- heterogeneous equality because the two sides lie over different
-- types (which are equal by Id′-AP).  We could instead coerce one
-- side or the other, but it seems more convenient for computing ap-AP
-- on concrete term-formers to not have the coercion (otherwise we'd
-- have to explicitly commute that coercion past all the
-- term-formers).  (If we ever had to remove the rewrite rules for AP₀
-- and AP₁, then Id′-AP would become heterogeneous too.)
postulate
  ap-AP : {Γ Δ : Tel} {A : el Δ → Type} (f : el Γ → el Δ) (g : (x : el Δ) → A x) (γ : el (ID Γ)) →
    ap g (AP f γ) ≡ʰ ap (λ w → g (f w)) γ

-- From this we can prove the analogous functoriality property for AP,
-- with some awful wrangling of heterogeneous exo-equality.
postulate
  AP-AP : {Γ Δ Θ : Tel} (f : el Γ → el Δ) (g : el Δ → el Θ) (γ : el (ID Γ)) →
    AP g (AP f γ) ≡ AP (λ w → g (f w)) γ
  AP-AP-ε : {Γ Δ : Tel} (f : el Γ → el Δ) (g : el Δ → el ε) (γ : el (ID Γ)) →
    AP-AP {Θ = ε} f g γ ≡ reflᵉ
  AP-AP-∷ : {Γ Δ Θ : Tel} (A : el Θ → Type) (f : el Γ → el Δ)
    (g : el Δ → el Θ) (h : (x : el Δ) → A (g x)) (γ : el (ID Γ)) →
    AP-AP f (λ x → g x ∷ h x) γ ≡
      ∷≡ (λ δaa → Id′ A (pop (pop δaa)) (top (pop δaa)) (top δaa))
      (∷≡ (λ δa → A ((pop δa)₁))
           (∷≡ (λ δ → A (δ ₀))
                (AP-AP f g γ)
                reflʰ)
           reflʰ)
       (coe→≡ʰ (Id′-AP g (AP f γ) A (h (f (γ ₀))) (h (f (γ ₁)))) _
       •ʰ ap-AP f h γ
       •ʰ revʰ (coe→≡ʰ (Id′-AP (λ x → g (f x)) γ A (h (f (γ ₀))) (h (f (γ ₁)))) _))

{-# REWRITE AP-AP-ε AP-AP-∷ #-}

-- Inspecting the above definition, we see that on a concrete
-- telescope, AP-AP consists essentially of reflexivities on points
-- and complex combinations of Id′-AP and ap-AP on identifications.
-- Thus, if the types and terms are also concrete, it should reduce
-- away to reflexivity too.

------------------------------
-- ap on variables
------------------------------

-- The action of ap on a variable appearing in the telescope is
-- supposed to be to project to the corresponding identification
-- argument.  (On variables not appearing in the telescope, it's
-- supposed to reduce to reflexivity, which we'll get to later.)  We
-- have no trouble distinguishing the "variables in the telescope"
-- since they are represented by De Bruijn indices using top and pop,
-- but we have to specify how to extract the correct identification.

-- Recall that identity telescopes are bundled and collated.  Thus, an
-- application like (ap (λ x → [n] x) δ), where [n] is a De Bruijn
-- index (represented as (top ∘ popⁿ)), should compute to [3n] δ,
-- picking out the correct identification component.  We obtain this by
-- computing in the following steps

-- ap (λ x → top (pop x)) δ
--   = top (AP (λ x → pop x) δ)
--   = top (pop (pop (pop (AP (λ x → x) δ)))))
--   = top (pop (pop (pop δ)))

-- Thus, we need to compute ap-top to top-AP, compute AP-pop to
-- pop-pop-pop-AP, and compute AP on the identity map to the identity.
-- We specify all three of these as postulated rewrite rules.

postulate
  AP-pop : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    AP (λ x → pop (f x)) γ ≡ pop (pop (pop (AP f γ)))

{-# REWRITE AP-pop #-}

-- Note that AP-pop is "one piece" of the originally proposed ▸-only
-- definition of AP.  Before we can postulate ap-top, we need to also
-- prove that all the other pieces of that definition also hold.
-- Since these aren't rewrites, we can phrase them as heterogeneous
-- equalities rather than equalities to a coercion.

-- TODO: Discuss.  Is this a nu-equation?
postulate
  pop-pop-pop₀ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID (Δ ▸ A))) →
    (pop (pop (pop δ)))₀ ≡ pop (δ ₀)
  pop-pop-pop₁ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID (Δ ▸ A))) →
    (pop (pop (pop δ)))₁ ≡ pop (δ ₁)

{-# REWRITE pop-pop-pop₀ pop-pop-pop₁ #-}

postulate
  top-pop-pop-AP : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ top (f (γ ₀))
  top-pop-AP : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ top (f (γ ₁))

{-# REWRITE top-pop-pop-AP top-pop-AP #-}

-- This combination means that (top-pop-pop-AP A f γ) actually
-- *always* reduces to reflʰ.  Unfortunately, since reflʰ doesn't
-- actually store its parameters as arguments, there is no way to
-- annotate it so that it will typecheck directly at the type of
-- (top-pop-pop-AP A f γ).  Thus, subject reduction fails.  However,
-- as noted before AP∷, this shouldn't be a problem in the
-- object-language fragment, where f will always be something
-- concrete.

postulate
  ap-top : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    ap (λ x → top (f x)) γ ≡
    coe← (Id′-AP≡ (λ x → pop (f x)) γ reflᵉ A reflʰ reflʰ)
         (top (AP f γ))

-- Now we can explain why the first argument of Σᵉ is a Tel rather
-- than a Typeᵉ: it enables ap-top to fire as a rewrite rule.  Look at
-- the LHS of ap-top, with implicit arguments included:

--  ap {Γ} {λ x → A (pop {Δ} {A} (f x))} (λ x → top {Δ} {A} (f x)) γ ≡

-- For the rewrite rule to fire, Agda has to be able to recognize
-- something of this form *and* deduce the values of all the arguments
-- (Γ, Δ, A, f, and γ) by higher-order pattern unification.  The way
-- we've set things up, this works because all of these arguments
-- appear bare (or, in the case of f, eta-expanded) as an argument of
-- a postulate in the above LHS.

-- However, if the first argument of Σᵉ were a Typeᵉ instead of a Tel,
-- and (el (Δ ▸ A)) reduced to (Σᵉ (el Δ) A) instead of (Σᵉ Δ A), then
-- the LHS of ap-top would be

--  ap {Γ} {λ x → A (pop {el Δ} {A} (f x))} (λ x → top {el Δ} {A} (f x)) γ ≡

-- Note that Δ now only appears inside of el.  Thus, this fails to
-- match instances where Δ is a concrete telescope, since then (el Δ)
-- would have been reduced to some iterated Σᵉ-exotype in which Δ
-- doesn't appear explicitly.

{-# REWRITE ap-top #-}

-- Note that we don't have rules for computing ap-top on "dependent
-- telescopes".  Hopefully this won't ever occur.

postulate
  AP-idmap : {Δ : Tel} (δ : el (ID Δ)) → AP {Δ} {Δ} (λ w → w) δ ≡ δ

{-# REWRITE AP-idmap #-}

-- It may seem like AP-idmap this should be provable, but I don't
-- think it is, because of how we've restricted AP to compute only on
-- terms like ∷ and pop.  However, we can make it reduce on endpoints.
AP-idmap₀ : {Δ : Tel} (δ : el (ID Δ)) → cong _₀ (AP-idmap δ) ≡ reflᵉ
AP-idmap₀ δ = axiomK

AP-idmap₁ : {Δ : Tel} (δ : el (ID Δ)) → cong _₁ (AP-idmap δ) ≡ reflᵉ
AP-idmap₁ δ = axiomK

{-# REWRITE AP-idmap₀ AP-idmap₁ #-}

-- With AP-idmap, we can compute the admissible rules like AP-AP and
-- Id′-AP on identities.
AP-AP-idmap : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
  AP-AP f (λ x → x) γ ≡ reflᵉ
AP-AP-idmap f γ = axiomK

AP-AP-idmap′ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) →
  AP-AP (λ x → x) f γ ≡ reflᵉ
AP-AP-idmap′ f γ = axiomK

Id′-AP-idmap : {Δ : Tel} (δ : el (ID Δ)) (A : el Δ → Type) (a₀ : A (δ ₀)) (a₁ : A (δ ₁)) →
  Id′-AP {Δ} {Δ} (λ w → w) δ A a₀ a₁ ≡ reflᵉ
Id′-AP-idmap δ A a₀ a₁ = axiomK

{-# REWRITE AP-AP-idmap AP-AP-idmap′ Id′-AP-idmap #-}
