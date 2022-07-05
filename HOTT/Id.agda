{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Id where

open import HOTT.Rewrite
open import HOTT.Telescope

--------------------------------------------------
-- Identity types and identity telescopes
--------------------------------------------------

-- Identity telescopes, collated and bundled.
ID : Tel → Tel

-- We define these mutually together with their projections to the
-- original telescope.
_₀ : {Δ : Tel} → el (ID Δ) → el Δ
_₁ : {Δ : Tel} → el (ID Δ) → el Δ
infix 60 _₀ _₁

-- We often want to wrap them up in the telescope function-space.
Λ₀ : {Δ : Tel} → (ID Δ) ⇨ᵉ el Δ
Λ₀ = (Λ x ⇨ᵉ x ₀)

Λ₁ : {Δ : Tel} → (ID Δ) ⇨ᵉ el Δ
Λ₁ = (Λ x ⇨ᵉ x ₁)

-- They are also mutual with the (postulated) dependent identity
-- *types* that they are composed of.
postulate
  -- Note that these depend on an element of the bundled (ID Δ), which
  -- consists of two points of Δ and an identification between them.
  Id : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID Δ)) (a₀ : A ⊘ (δ ₀)) (a₁ : A ⊘ (δ ₁)) → Type

ID▸▸ : {Δ : Tel} (A : Δ ⇨ Type) → Tel
ID▸▸ {Δ} A = ID Δ ▸ (A ⊚ Λ₀) ▸ (A ⊚ Λ₁ ⊚ᵉ POP)

Id/ : {Δ : Tel} (A : Δ ⇨ Type) → ID▸▸ A ⇨ Type
Id/ A = (Λ x ⇨ Id A (pop (pop x)) (top (pop x)) (top x))

ID ε = ε
ID (Δ ▸ A) = ID▸▸ A ▸ Id/ A

_₀ {ε} _ = []
_₀ {Δ ▸ A} (δ ∷ a₀ ∷ a₁ ∷ a₂) = δ ₀ ∷ a₀

_₁ {ε} _ = []
_₁ {Δ ▸ A} (δ ∷ a₀ ∷ a₁ ∷ a₂) = δ ₁ ∷ a₁

-- Congruence for dependent identity types
Id≡ : {Δ : Tel} (A : Δ ⇨ Type)
    {γ δ : el (ID Δ)} (e : γ ≡ᵉ δ)
    {a₀ : A ⊘ (γ ₀)} {b₀ : A ⊘ (δ ₀)} (e₀ : a₀ ≡ʰ b₀)
    {a₁ : A ⊘ (γ ₁)} {b₁ : A ⊘ (δ ₁)} (e₁ : a₁ ≡ʰ b₁) →
    Id A γ a₀ a₁ ≡ Id A δ b₀ b₁
Id≡ _ reflᵉᵉ reflʰ reflʰ = reflᵉ

-- And for elements of an identity telescope
ID∷≡ : {Δ : Tel} (A : Δ ⇨ Type)
       {δ δ' : el (ID Δ)} (ϕ : δ ≡ᵉ δ')
       {a₀ : A ⊘ (δ ₀)} {a₀' : A ⊘ (δ' ₀)} (e₀ : a₀ ≡ʰ a₀')
       {a₁ : A ⊘ (δ ₁)} {a₁' : A ⊘ (δ' ₁)} (e₁ : a₁ ≡ʰ a₁')
       {a₂ : Id A δ a₀ a₁} {a₂' : Id A δ' a₀' a₁'} (e₂ : a₂ ≡ʰ a₂') →
       _≡ᵉ_ {el (ID (Δ ▸ A))} (δ ∷ a₀ ∷ a₁ ∷ a₂) (δ' ∷ a₀' ∷ a₁' ∷ a₂')
ID∷≡ A reflᵉᵉ reflʰ reflʰ reflʰ = reflᵉᵉ

----------------------------------------
-- ap, AP, and functoriality of Id
----------------------------------------

postulate
  -- Since the non-dependent identity types _＝_ will be
  -- definitionally a special case of Id, we don't need separate and
  -- non-dependent versions of ap.  Note that like Id, it depends on
  -- an element of the bundled (ID Δ).  Note also that the telescope
  -- function-space A is an explicit argument.
  ap : {Δ : Tel} (A : Δ ⇨ Type) (f : (x : el Δ) → A ⊘ x) (δ : el (ID Δ)) →
    Id A δ (f (δ ₀)) (f (δ ₁))

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
  AP : {Γ Δ : Tel} (f : Γ ⇨ᵉ el Δ) (γ : el (ID Γ)) → el (ID Δ)

-- We "define" AP mutually with the assertions that its projections
-- are the action of the original f on the projections.  We could
-- *prove* these, mutually with the other definitions in this block.
-- But we want to declare them as rewrites eventually anyway, and
-- carrying around terms for them causes things to blow up and slow
-- down.  So we just postulate them as rewrites.
postulate
  AP₀ : {Γ Δ : Tel} (f : Γ ⇨ᵉ el Δ) (γ : el (ID Γ)) → (AP f γ)₀ ≡ᵉ f ⊘ᵉ (γ ₀)
  AP₁ : {Γ Δ : Tel} (f : Γ ⇨ᵉ el Δ) (γ : el (ID Γ)) → (AP f γ)₁ ≡ᵉ f ⊘ᵉ (γ ₁)

{-# REWRITE AP₀ AP₁ #-}

-- For AP to be well-defined, we also need to mutually prove/postulate
-- its behavior on identity maps and pops, and its naturality.  Of
-- these, AP-pop and AP-idmap are "real" computation rules, which are
-- 2/3 of how we specify the behavior of AP on our De Bruijn variables
-- in telescopes.  The other 1/3 is ap-top, which requires other
-- things so we postpone it to below.
postulate
  AP-idmap : {Δ : Tel} (δ : el (ID Δ)) → AP {Δ} {Δ} IDMAP δ ≡ᵉ δ
  AP-pop : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    AP (Λ x ⇨ᵉ pop (f x)) γ ≡ᵉ pop (pop (pop (AP (Λ⇨ᵉ f) γ)))

{-# REWRITE AP-idmap AP-pop #-}

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
-- automatically.  However, the most natural type of Id-AP:
--- Id (λ x → A (f x)) γ a₀ a₁ ≡ Id A (AP f γ) a₀ a₁
-- is not rewritable from left to right, since (A (f x)) doesn't have
-- A and f in pattern position.

-- One approach that I tried is to reverse this equality, since the
-- right-hand side does have A and f in pattern position.  This does
-- improve the situation, but it can still often fail to match,
-- because AP is volatile and might be reduced to something that Agda
-- can't un-rewrite in order to match.

-- Currently we're taking a different approach: by introducing the
-- separate telescope function-space datatype, with a postulated
-- composition operation ⊚, we can force the left-hand side to be
-- matchable.  Relative to reversing the equality, this removes some
-- coercions (e.g. all four identifications in the boundary of a
-- square in type A are actually identifications in A itself, rather
-- than some substituted version of it), but introduces others
-- (e.g. in the definitions of ap on pairs and snd).  It's not
-- entirely obvious to me which is better overall; I do like not
-- having to coerce the boundary of a square, but this way definitely
-- has more technical overhead, and seems to require the codomain of
-- ap to be explicit, which is annoying.

postulate
  -- This is intentionally not (f : Γ ⇨ Δ), to match more generally.
  Id-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : Δ ⇨ Type)
          (a₀ : A ⊘ (f (γ ₀))) (a₁ : A ⊘ (f (γ ₁))) →
    Id (Λ x ⇨ A ⊘ f x) γ a₀ a₁ ≡ Id A (AP (Λ⇨ᵉ f) γ) a₀ a₁
  Id-AP⊚ : {Γ Δ : Tel} (f : Γ ⇨ᵉ el Δ) (γ : el (ID Γ)) (A : Δ ⇨ Type)
          (a₀ : A ⊘ (f ⊘ᵉ (γ ₀))) (a₁ : A ⊘ (f ⊘ᵉ (γ ₁))) →
    Id (A ⊚ f) γ a₀ a₁ ≡ Id A (AP f γ) a₀ a₁

{-# REWRITE Id-AP Id-AP⊚ #-}

-- Having Id-AP as a rewrite is at least sufficient for us to be able
-- to "define" AP without any coercions.
postulate
  APε : {Γ : Tel} (f : Γ ⇨ᵉ el ε) (γ : el (ID Γ)) → AP {Δ = ε} f γ ≡ᵉ []
  -- This is intentionally not a ⇨, to match more generally.
  AP∷ : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el Δ) (A : Δ ⇨ Type) (g : (x : el Γ) → A ⊘ (f x)) →
    AP {Δ = Δ ▸ A} (Λ x ⇨ᵉ f x ∷ g x) γ ≡ᵉ
    AP (Λ⇨ᵉ f) γ ∷ g (γ ₀) ∷ g (γ ₁) ∷ ap (A ⊚ (Λ⇨ᵉ f)) g γ 

{-# REWRITE APε AP∷ #-}

-- Since Id-AP⊚ always fires as a rewrite, we don't need to coerce
-- along it by hand.  But sometimes we do need to coerce along Id-AP
-- by hand, since the LHS ⊘ can be reduced and unmatchable.  However,
-- if we declare it to reduce to reflᵉ, then such coercions will
-- disappear, as we expect them to do in concrete cases where Id-AP
-- should hold by definition anyway.
Id-AP-reflᵉ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : Δ ⇨ Type)
  (a₀ : A ⊘ (f (γ ₀))) (a₁ : A ⊘ (f (γ ₁))) →
  Id-AP f γ A a₀ a₁ ≡ᵉ reflᵉ
Id-AP-reflᵉ f γ A a₀ a₁ = axiomK

{-# REWRITE Id-AP-reflᵉ #-}

------------------------------
-- Functoriality of ap and AP
------------------------------

postulate
  -- We treat functoriality of AP the same way we did the naturality
  -- of Id, as above.
  AP-AP : {Γ Δ Θ : Tel} (f : Γ ⇨ᵉ el Δ) (g : Δ ⇨ᵉ el Θ) (γ : el (ID Γ)) →
    AP (Λ x ⇨ᵉ g ⊘ᵉ (f ⊘ᵉ x)) γ ≡ᵉ AP g (AP f γ)
  AP-AP⊚ : {Γ Δ Θ : Tel} (f : Γ ⇨ᵉ el Δ) (g : Δ ⇨ᵉ el Θ) (γ : el (ID Γ)) →
    AP (g ⊚ᵉ f) γ ≡ᵉ AP g (AP f γ)
  -- For functoriality of ap, we declare the rewrites to go in the
  -- other direction, since we don't have a dependent ⊚ to be the
  -- "composite" of g and f.
  ap-AP : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : Γ ⇨ᵉ el Δ) (g : (x : el Δ) → A ⊘ x)
          (γ : el (ID Γ)) →
    ap A g (AP f γ) ≡ ap (Λ x ⇨ A ⊘ (f ⊘ᵉ x)) (λ w → g (f ⊘ᵉ w)) γ
  ap-AP′ : {Γ Δ : Tel} {A : el Δ → Type} (f : el Γ → el Δ) (g : (x : el Δ) → A x)
          (γ : el (ID Γ)) →
    ap (Λ⇨ A) g (AP (Λ⇨ᵉ f) γ) ≡ ap (Λ⇨ A ⊚ Λ⇨ᵉ f) (λ w → g (f w)) γ
  -- In case the codomain family is given as a composite, we
  -- eta-expand it out so that the above rewrites can match.
  ap⊚ : {Γ Δ : Tel} {A : Δ ⇨ Type} (f : Γ ⇨ᵉ el Δ)
    (g : (x : el Γ) → A ⊘ (f ⊘ᵉ x)) (γ : el (ID Γ)) →
    ap (A ⊚ f) g γ ≡ ap (Λ x ⇨ A ⊘ (f ⊘ᵉ x)) g γ

{-# REWRITE ap-AP ap-AP′ AP-AP AP-AP⊚ ap⊚ #-}

-- Since ap-AP is rewritten in the backwards direction and AP is
-- volatile, we declare some special cases as additional rewrites to
-- deal with the possible appearance of reduced APs.

ap-AP∷ : {Γ Δ : Tel} (B : Δ ⇨ Type) (A : (Δ ▸ B) ⇨ Type)
  (f : el Γ → el Δ) (h : (x : el Γ) → B ⊘ (f x))
  (g : (x : el (Δ ▸ B)) → A ⊘ x) (γ : el (ID Γ)) →
  ap A g (AP (Λ⇨ᵉ f) γ ∷ h (γ ₀) ∷ h (γ ₁) ∷ ap (B ⊚ Λ⇨ᵉ f) h γ) ≡
  ap (A ⊚ (Λ x ⇨ᵉ f x ∷ h x)) (λ w → g (f w ∷ h w)) γ
ap-AP∷ B A f h g γ = ap-AP A (Λ x ⇨ᵉ f x ∷ h x) g γ

ap-AP-idmap∷ : {Δ : Tel} (B : Δ ⇨ Type) (A : (Δ ▸ B) ⇨ Type)
  (h : (x : el Δ) → B ⊘ x)
  (g : (x : el (Δ ▸ B)) → A ⊘ x) (γ : el (ID Δ)) →
  ap A g (γ ∷ h (γ ₀) ∷ h (γ ₁) ∷ ap (B) h γ) ≡
  ap (A ⊚ (Λ x ⇨ᵉ x ∷ h x)) (λ w → g (w ∷ h w)) γ
ap-AP-idmap∷ B A h g γ = ap-AP A (Λ x ⇨ᵉ x ∷ h x) g γ

{-# REWRITE ap-AP∷ ap-AP-idmap∷ #-}

-- As with Id-AP, we declare AP-AP to reduce to reflᵉᵉ so that it
-- disappears on concrete terms like it should.
AP-AP-reflᵉ : {Γ Δ Θ : Tel} (f : Γ ⇨ᵉ el Δ) (g : Δ ⇨ᵉ el Θ) (γ : el (ID Γ)) →
  AP-AP f g γ ≡ᵉ reflᵉᵉ
AP-AP-reflᵉ f g γ = axiomKᵉ

{-# REWRITE AP-AP-reflᵉ #-}

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
  pop-pop-pop₀ : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID (Δ ▸ A))) →
    (pop (pop (pop δ)))₀ ≡ᵉ pop {B = A} (δ ₀)
  pop-pop-pop₁ : {Δ : Tel} (A : Δ ⇨ Type) (δ : el (ID (Δ ▸ A))) →
    (pop (pop (pop δ)))₁ ≡ᵉ pop {B = A} (δ ₁)

{-# REWRITE pop-pop-pop₀ pop-pop-pop₁ #-}

-- Here are the other two pieces of the ▸-only definition of AP.
postulate
  top-pop-pop-AP : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : Γ ⇨ᵉ el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ top (f ⊘ᵉ (γ ₀))
  top-pop-AP : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : Γ ⇨ᵉ el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ top (f ⊘ᵉ (γ ₁))

{-# REWRITE top-pop-pop-AP top-pop-AP #-}

-- Finally, we can postulate ap-top.
postulate
  ap-top : {Γ Δ : Tel} (A : Δ ⇨ Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    ap (Λ x ⇨ A ⊘ pop (f x)) (λ x → top (f x)) γ ≡ top (AP (Λ⇨ᵉ f) γ)
  ap-top′ : {Γ Δ : Tel} (A : el Δ → Type)
    (f : el Γ → el (Δ ▸ (Λ⇨ A))) (γ : el (ID Γ)) →
    ap (Λ x ⇨ A (pop (f x))) (λ x → top (f x)) γ ≡
    coe← (Id-AP (λ x → pop (f x)) γ (Λ⇨ A) (top (f (γ ₀))) (top (f (γ ₁))))
          (top (AP (Λ⇨ᵉ f) γ))

{-# REWRITE ap-top ap-top′ #-}

-- Now we can explain why the first argument of _▹_ is a Tel rather
-- than a Typeᵉ: it enables ap-top to fire as a rewrite rule.  Look at
-- the LHS of ap-top, with implicit arguments included:

--  ap {Γ} {λ x → A (pop {Δ} {A} (f x))} (λ x → top {Δ} {A} (f x)) γ ≡

-- For the rewrite rule to fire, Agda has to be able to recognize
-- something of this form *and* deduce the values of all the arguments
-- (Γ, Δ, A, f, and γ) by higher-order pattern unification.  The way
-- we've set things up, this works because all of these arguments
-- appear bare (or, in the case of f, eta-expanded) as an argument of
-- a postulate in the above LHS.

-- However, if the first argument of _▹_ were a Typeᵉ instead of a Tel,
-- and (el (Δ ▸ A)) reduced to (el Δ ▹ A) instead of (Δ ▹ A), then
-- the LHS of ap-top would be

--  ap {Γ} {λ x → A (pop {el Δ} {A} (f x))} (λ x → top {el Δ} {A} (f x)) γ ≡

-- Note that Δ now only appears inside of el.  Thus, this fails to
-- match instances where Δ is a concrete telescope, since then (el Δ)
-- would have been reduced to some iterated Σ-exotype in which Δ
-- doesn't appear explicitly.

-- Note that we don't have rules for computing ap-top on "dependent
-- telescopes".  Hopefully this won't ever occur.
