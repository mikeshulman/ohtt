{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

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
  Id : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀)) (a₁ : A (δ ₁)) → Type

ID ε = ε
ID (Δ ▸ A) = ID Δ ▸ (λ δ → A (δ ₀)) ▸ (λ δa → A ((pop δa)₁)) ▸ (λ δaa → Id A (pop (pop δaa)) (top (pop δaa)) (top δaa))

_₀ {ε} _ = []
_₀ {Δ ▸ A} (δ ∷ a₀ ∷ a₁ ∷ a₂) = δ ₀ ∷ a₀

_₁ {ε} _ = []
_₁ {Δ ▸ A} (δ ∷ a₀ ∷ a₁ ∷ a₂) = δ ₁ ∷ a₁

-- Congruence for dependent identity types
Id≡ : {Δ : Tel} (A : el Δ → Type)
    {γ δ : el (ID Δ)} (e : γ ≡ᵉ δ)
    {a₀ : A (γ ₀)} {b₀ : A (δ ₀)} (e₀ : a₀ ≡ʰ b₀)
    {a₁ : A (γ ₁)} {b₁ : A (δ ₁)} (e₁ : a₁ ≡ʰ b₁) →
    Id A γ a₀ a₁ ≡ Id A δ b₀ b₁
Id≡ _ reflᵉᵉ reflʰ reflʰ = reflᵉ

-- And for elements of an identity telescope
ID∷≡ : {Δ : Tel} (A : el Δ → Type)
       {δ δ' : el (ID Δ)} (ϕ : δ ≡ᵉ δ')
       {a₀ : A (δ ₀)} {a₀' : A (δ' ₀)} (e₀ : a₀ ≡ʰ a₀')
       {a₁ : A (δ ₁)} {a₁' : A (δ' ₁)} (e₁ : a₁ ≡ʰ a₁')
       {a₂ : Id A δ a₀ a₁} {a₂' : Id A δ' a₀' a₁'} (e₂ : a₂ ≡ʰ a₂') →
       _≡ᵉ_ {el (ID (Δ ▸ A))} (δ ∷ a₀ ∷ a₁ ∷ a₂) (δ' ∷ a₀' ∷ a₁' ∷ a₂')
ID∷≡ A reflᵉᵉ reflʰ reflʰ reflʰ = reflᵉᵉ

----------------------------------------
-- ap, AP, and functoriality of Id
----------------------------------------

postulate
  -- Since Id will be definitionally a special case of Id, we don't
  -- need separate and non-dependent versions of ap.  Note that like
  -- Id, it depends on an element of the bundled (ID Δ).
  ap : {Δ : Tel} {A : el Δ → Type} (f : (δ : el Δ) → A δ) (δ : el (ID Δ)) → Id A δ (f (δ ₀)) (f (δ ₁))

-- Telescope AP.  I hope we can get away with only the non-dependent
-- version.  We'd like to *define* it by recursion on the target:
{-
AP {Δ = ε} f γ = []
AP {Δ = Δ ▸ A} f γ = AP (λ x → pop (f x)) γ ∷ top (f (γ ₀)) ∷ top (f (γ ₁)) ∷ ap (λ x → top (f x)) γ
-}
-- However, in order to get ap to compute on variables, we need AP to
-- compute on pop, and if it also computed on arbitrary telescopes
-- that would produce infinite loops.  (You can see an AP-pop redex in
-- the above definition.)  So instead we "define" AP to compute in
-- this way only when the *term* is also of the form ∷.  This requires
-- matching inside a λ, so it has to be done with rewrite rules.  Note
-- that this is a *syntactic* restriction, not a semantic one: since ∷
-- satisfies an eta-rule (which is a rewrite contraction, not a record
-- expansion), the two definitions have the same semantics.
postulate
  AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → el (ID Δ)

-- We "define" AP mutually with the assertions that its projections
-- are the action of the original f on the projections.  We could
-- *prove* these, mutually with the other definitions in this block.
-- But we want to declare them as rewrites eventually anyway, and
-- carrying around terms for them causes things to blow up and slow
-- down.  So we just postulate them as rewrites.
postulate
  AP₀ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → (AP f γ)₀ ≡ᵉ f (γ ₀)
  AP₁ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → (AP f γ)₁ ≡ᵉ f (γ ₁)

{-# REWRITE AP₀ AP₁ #-}

-- For AP to be well-defined, we also need to mutually prove/postulate
-- its behavior on identity maps and pops, and its naturality.
postulate
  AP-idmap : {Δ : Tel} (δ : el (ID Δ)) → AP {Δ} {Δ} (λ w → w) δ ≡ᵉ δ
  AP-pop : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    AP (λ x → pop (f x)) γ ≡ᵉ pop (pop (pop (AP f γ)))
  Id-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : el Δ → Type) (a₀ : A (f (γ ₀))) (a₁ : A (f (γ ₁))) →
    Id A (AP f γ) a₀ a₁ ≡ Id (λ w → A (f w)) γ a₀ a₁

-- Of these, AP-pop and AP-idmap are "real" computation rules, which
-- are 2/3 of how we specify the behavior of AP on our De Bruijn
-- variables in telescopes.  The other 1/3 is ap-top, which requires
-- other things so we postpone it to below.

-- Id-AP, on the other hand, is morally an *admissible* equality,
-- proven by induction on the type formers constituting A.  The "more
-- correct" way to deal with it would be to postulate it as an
-- exo-equality and give rewrite rules saying how this exo-equality
-- *computes* on different type-formers in A, thereby essentially
-- implementing the proof of admissibility.  But we would then have to
-- coerce along that exo-equality explicitly in lots of places (at
-- least, in the framework code), making for annoying coding, large
-- terms, and slower typechecking.

-- We can alleviate some of that (though not all) by declaring Id-AP
-- as a rewrite, so that *sometimes* Agda will be able to apply it
-- automatically so we don't have to coerce.  The direction chosen
-- above, though arguably morally the "less right" direction, is the
-- only possible direction for this, since Agda can't match against
-- the RHS to rewrite.  Sometimes it fails to match against the LHS
-- too, since AP is volatile and might be reduced to something that
-- Agda can't un-rewrite in order to match; thus we have to either
-- coerce explicitly or use additional rewrite lemmas.

{-# REWRITE AP-idmap AP-pop Id-AP #-}

-- Having Id-AP as a rewrite is at least sufficient for us to be able
-- to "define" AP without any coercions.
postulate
  APε : {Γ : Tel} (f : el Γ → el ε) (γ : el (ID Γ)) → AP {Δ = ε} f γ ≡ᵉ []
  AP∷ : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el Δ) (A : el Δ → Type) (g : (x : el Γ) → A (f x)) →
    AP {Δ = Δ ▸ A} (λ x → f x ∷ g x) γ ≡ᵉ
    AP f γ ∷ g (γ ₀) ∷ g (γ ₁) ∷ ap g γ

{-# REWRITE APε AP∷ #-}

----------------------------------------
-- Auxiliary forms of Id-naturality
----------------------------------------

-- We give special names to coercion along Id-AP for pop, since it
-- happens a lot.

Id-pop→ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
  {b₀ : B (δ ₀)} {b₁ : B (δ ₁)} (b₂ : Id B δ b₀ b₁)
  {a₀ : A (δ ₀)} {a₁ : A (δ ₁)} →
  Id A δ a₀ a₁ → Id (λ x → A (pop x)) (δ ∷ b₀ ∷ b₁ ∷ b₂) a₀ a₁
Id-pop→ {Δ} A B δ {b₀} {b₁} b₂ {a₀} {a₁} a₂ = coe→ (Id-AP {Δ ▸ B} (λ x → pop x) (δ ∷ b₀ ∷ b₁ ∷ b₂) A a₀ a₁) a₂

Id-pop← : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
  {b₀ : B (δ ₀)} {b₁ : B (δ ₁)} (b₂ : Id B δ b₀ b₁)
  {a₀ : A (δ ₀)} {a₁ : A (δ ₁)} →
  Id (λ x → A (pop x)) (δ ∷ b₀ ∷ b₁ ∷ b₂) a₀ a₁ → Id A δ a₀ a₁
Id-pop← {Δ} A B δ {b₀} {b₁} b₂ {a₀} {a₁} a₂ = coe← (Id-AP {Δ ▸ B} (λ x → pop x) (δ ∷ b₀ ∷ b₁ ∷ b₂) A a₀ a₁) a₂

Id-pop→≡ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
  {b₀ : B (δ ₀)} {b₁ : B (δ ₁)} (b₂ : Id B δ b₀ b₁)
  {a₀ : A (δ ₀)} {a₁ : A (δ ₁)} (a₂ : Id A δ a₀ a₁) →
  Id-pop→ {Δ} A B δ {b₀} {b₁} b₂ {a₀} {a₁} a₂ ≡ʰ a₂
Id-pop→≡  {Δ} A B δ {b₀} {b₁} b₂ {a₀} {a₁} a₂ = coe→≡ʰ (Id-AP {Δ ▸ B} (λ x → pop x) (δ ∷ b₀ ∷ b₁ ∷ b₂) A a₀ a₁) a₂

Id-pop←≡ : {Δ : Tel} (A B : el Δ → Type) (δ : el (ID Δ))
  {b₀ : B (δ ₀)} {b₁ : B (δ ₁)} (b₂ : Id B δ b₀ b₁)
  {a₀ : A (δ ₀)} {a₁ : A (δ ₁)} (a₂ : Id (λ x → A (pop x)) (δ ∷ b₀ ∷ b₁ ∷ b₂) a₀ a₁) →
  Id-pop← {Δ} A B δ {b₀} {b₁} b₂ {a₀} {a₁} a₂ ≡ʰ a₂
Id-pop←≡ {Δ} A B δ {b₀} {b₁} b₂ {a₀} {a₁} a₂ = coe←≡ʰ (Id-AP {Δ ▸ B} (λ x → pop x) (δ ∷ b₀ ∷ b₁ ∷ b₂) A a₀ a₁) a₂

-- We also declare that not only is Id-AP a rewrite, it itself
-- rewrites to reflᵉ.  Thus, the coercions we are sometimes forced to
-- insert to make things typecheck will vanish when the term is
-- normalized.  This is consistent because on concrete types, Id-AP
-- should hold definitionally.

Id-AP-reflᵉ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : el Δ → Type) (a₀ : A (f (γ ₀))) (a₁ : A (f (γ ₁))) →
  Id-AP f γ A a₀ a₁ ≡ᵉ reflᵉ
Id-AP-reflᵉ f γ A a₀ a₁ = axiomK

{-# REWRITE Id-AP-reflᵉ #-}

-- As noted above, the AP on the LHS of Id-AP is volatile and could
-- appear in a reduced form.  To assist with this, we assert more
-- rewrites applying directly to this case with a reduced AP.
postulate
  Id-AP▸ : {Γ Δ : Tel} (B : el Δ → Type) (f : el Γ → el Δ) (g : (x : el Γ) → B (f x)) (γ : el (ID Γ))
    (A : el (Δ ▸ B) → Type) (a₀ : A (f (γ ₀) ∷ g (γ ₀))) (a₁ : A (f (γ ₁) ∷ g (γ ₁))) →
    Id A (AP f γ ∷ g (γ ₀) ∷ g (γ ₁) ∷ ap g γ) a₀ a₁ ≡ Id (λ w → A (f w ∷ g w)) γ a₀ a₁
  Id-AP-idmap▸ : {Δ : Tel} (B : el Δ → Type) (g : (x : el Δ) → B x) (γ : el (ID Δ))
    (A : el (Δ ▸ B) → Type) (a₀ : A (γ ₀ ∷ g (γ ₀))) (a₁ : A (γ ₁ ∷ g (γ ₁))) →
    Id A (γ ∷ g (γ ₀) ∷ g (γ ₁) ∷ ap g γ) a₀ a₁ ≡ Id (λ w → A (w ∷ g w)) γ a₀ a₁

{-# REWRITE Id-AP▸ Id-AP-idmap▸ #-}

-- We could also have AP reduced more than once.  Obviously there is a
-- potentially infinite family of rewrites here, but we don't need all
-- of them; we just need enough that we can write down and typecheck
-- the rest of the theory.  For concrete usage *in* the theory, as
-- noted before, Id-AP should hold definitionally anyway.
postulate
  Id-AP▸▸ : {Γ Δ : Tel} (B : el Δ → Type) (C : el (Δ ▸ B) → Type)
    (f : el Γ → el Δ) (g : (x : el Γ) → B (f x)) (h : (x : el Γ) → C (f x ∷ g x)) (γ : el (ID Γ))
    (A : el (Δ ▸ B ▸ C) → Type) (a₀ : A (f (γ ₀) ∷ g (γ ₀) ∷ h (γ ₀))) (a₁ : A (f (γ ₁) ∷ g (γ ₁) ∷ h (γ ₁))) →
    Id A (AP f γ ∷ g (γ ₀) ∷ g (γ ₁) ∷ ap g γ ∷ h (γ ₀) ∷ h (γ ₁) ∷ ap h γ) a₀ a₁ ≡ Id (λ w → A (f w ∷ g w ∷ h w)) γ a₀ a₁

{-# REWRITE Id-AP▸▸ #-}

Id-AP▸-reflᵉ : {Γ Δ : Tel} (B : el Δ → Type)
  (f : el Γ → el Δ) (g : (x : el Γ) → B (f x)) (γ : el (ID Γ))
  (A : el (Δ ▸ B) → Type) (a₀ : A (f (γ ₀) ∷ g (γ ₀))) (a₁ : A (f (γ ₁) ∷ g (γ ₁))) →
  Id-AP▸ B f g γ A a₀ a₁ ≡ᵉ reflᵉ
Id-AP▸-reflᵉ  B f g γ A a₀ a₁ = axiomK

Id-AP-idmap▸-reflᵉ : {Δ : Tel} (B : el Δ → Type) (g : (x : el Δ) → B x) (γ : el (ID Δ))
  (A : el (Δ ▸ B) → Type) (a₀ : A (γ ₀ ∷ g (γ ₀))) (a₁ : A (γ ₁ ∷ g (γ ₁))) →
  Id-AP-idmap▸ B g γ A a₀ a₁ ≡ᵉ reflᵉ
Id-AP-idmap▸-reflᵉ B g γ A a₀ a₁ = axiomK

Id-AP▸▸-reflᵉ : {Γ Δ : Tel} (B : el Δ → Type) (C : el (Δ ▸ B) → Type)
  (f : el Γ → el Δ) (g : (x : el Γ) → B (f x)) (h : (x : el Γ) → C (f x ∷ g x)) (γ : el (ID Γ))
  (A : el (Δ ▸ B ▸ C) → Type) (a₀ : A (f (γ ₀) ∷ g (γ ₀) ∷ h (γ ₀))) (a₁ : A (f (γ ₁) ∷ g (γ ₁) ∷ h (γ ₁))) →
  Id-AP▸▸ B C f g h γ A a₀ a₁ ≡ᵉ reflᵉ
Id-AP▸▸-reflᵉ B C f g h γ A a₀ a₁ = axiomK

{-# REWRITE Id-AP▸-reflᵉ Id-AP-idmap▸-reflᵉ Id-AP▸▸-reflᵉ #-}

------------------------------
-- Functoriality of ap and AP
------------------------------

postulate
  ap-AP : {Γ Δ : Tel} {A : el Δ → Type} (f : el Γ → el Δ) (g : (x : el Δ) → A x) (γ : el (ID Γ)) →
    ap g (AP f γ) ≡ ap (λ w → g (f w)) γ
  AP-AP : {Γ Δ Θ : Tel} (f : el Γ → el Δ) (g : el Δ → el Θ) (γ : el (ID Γ)) →
    AP g (AP f γ) ≡ᵉ AP (λ w → g (f w)) γ

{-# REWRITE ap-AP AP-AP #-}

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

-- Note that AP-pop is "one piece" of the originally proposed ▸-only
-- definition of AP.  Before we can postulate ap-top, we need to also
-- postulate that all the other pieces of that definition also hold.
-- And before that, we have to explain how _₀ and _₁ commute with pop.
-- These can be regarded as "nu-eqquations" that hold automatically on
-- concrete terms, and are enforced to hold also for neutral terms by
-- rewrites.

postulate
  pop-pop-pop₀ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID (Δ ▸ A))) →
    (pop (pop (pop δ)))₀ ≡ᵉ pop (δ ₀)
  pop-pop-pop₁ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID (Δ ▸ A))) →
    (pop (pop (pop δ)))₁ ≡ᵉ pop (δ ₁)

{-# REWRITE pop-pop-pop₀ pop-pop-pop₁ #-}

-- Here are the other two pieces of the ▸-only definition of AP.
postulate
  top-pop-pop-AP : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ top (f (γ ₀))
  top-pop-AP : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ top (f (γ ₁))

{-# REWRITE top-pop-pop-AP top-pop-AP #-}

-- We also need a specialized version of Id on pop.
postulate
  Id-AP-pop³-AP : {Γ Δ : Tel} (A B : el Δ → Type) (f : el Γ → el (Δ ▸ B)) (γ : el (ID Γ))
    (a₀ : A (pop (f (γ ₀)))) (a₁ : A (pop (f (γ ₁)))) →
    Id A (pop (pop (pop (AP f γ)))) a₀ a₁ ≡ Id (λ w → A (pop (f w))) γ a₀ a₁

{-# REWRITE Id-AP-pop³-AP #-}

-- Finally, we can postulate ap-top.
postulate
  ap-top : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    ap (λ x → top (f x)) γ ≡ top (AP f γ) 

{-# REWRITE ap-top #-}

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

-- Note that we don't have rules for computing ap-top on "dependent
-- telescopes".  Hopefully this won't ever occur.
