{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

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
_₀ {Δ ▸ A} δ = (pop (pop (pop δ)))₀ ∷ top (pop (pop δ))

_₁ {ε} _ = []
_₁ {Δ ▸ A} δ = (pop (pop (pop δ)))₁ ∷ top (pop δ)

-- Congruence for dependent identity types
Id′≡ : {Δ : Tel} (A : el Δ → Type)
    {γ δ : el (ID Δ)} (e : γ ≡ δ)
    {a₀ : A (γ ₀)} {b₀ : A (δ ₀)} (e₀ : a₀ ≡ʰ b₀)
    {a₁ : A (γ ₁)} {b₁ : A (δ ₁)} (e₁ : a₁ ≡ʰ b₁) →
    Id′ A γ a₀ a₁ ≡ Id′ A δ b₀ b₁
Id′≡ _ reflᵉ reflʰ reflʰ = reflᵉ

----------------------------------------
-- Telescope ap and functoriality, I
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
AP₀ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → (AP f γ)₀ ≡ f (γ ₀)
AP₁ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → (AP f γ)₁ ≡ f (γ ₁)

-- We also define AP mutually with postulated naturality for Id′.
-- This rule should be admissible, meaning we will give rewrite rules
-- making it hold definitionally on all concrete telescopes and terms.
-- Specifically, Id′-AP should compute on types, like Id′.
postulate
  Id′-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : el Δ → Type) (a₀ : A (f (γ ₀))) (a₁ : A (f (γ ₁))) →
    Id′ (λ w → A (f w)) γ a₀ a₁ ≡ Id′ A (AP f γ) (coe← (cong A (AP₀ f γ)) a₀) (coe← (cong A (AP₁ f γ)) a₁)

-- Note that in defining AP, we have to coerce along AP₀, AP₁ and
-- Id′-AP, justifying the mutual definition.
postulate
  APε : {Γ : Tel} (f : el Γ → el ε) (γ : el (ID Γ)) → AP {Δ = ε} f γ ≡ []
  AP∷ : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el Δ) (A : el Δ → Type) (g : (x : el Γ) → A (f x)) →
    AP {Δ = Δ ▸ A} (λ x → f x ∷ g x) γ ≡
      AP f γ ∷
      coe← (cong A (AP₀ f γ)) (g (γ ₀)) ∷
      coe← (cong A (AP₁ f γ)) (g (γ ₁)) ∷
      coe→ (Id′-AP f γ A (g (γ ₀)) (g (γ ₁))) (ap g γ)

{-# REWRITE APε AP∷ #-}

-- AP₀ and AP₁ also have to be "defined" on ∷ by matching inside λ.
-- But since ∷ has an eta-rule, and we don't care about preventing
-- computation on non-constructors, it suffices to decompose the
-- argument with top and pop and pass it off to a helper function.
AP₀∷ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el Δ) (g : (x : el Γ) → A (f x)) (γ : el (ID Γ)) →
  (AP (λ x → f x ∷ g x) γ)₀ ≡ f (γ ₀) ∷ g (γ ₀)
AP₀∷ A f g γ = ∷≡ A (AP₀ f γ) (coe←≡ʰ (cong A (AP₀ f γ)) (g (γ ₀)))

AP₁∷ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el Δ) (g : (x : el Γ) → A (f x)) (γ : el (ID Γ)) →
  ((AP (λ x → f x ∷ g x) γ)₁) ≡ f (γ ₁) ∷ g (γ ₁)
AP₁∷ A f g γ = ∷≡ A (AP₁ f γ) (coe←≡ʰ (cong A (AP₁ f γ)) (g (γ ₁)))

AP₀ {Δ = ε} f γ = reflᵉ
AP₀ {Δ = Δ ▸ A} f γ = AP₀∷ A (λ x → pop (f x)) (λ x → top (f x)) γ
AP₁ {Δ = ε} f γ = reflᵉ
AP₁ {Δ = Δ ▸ A} f γ = AP₁∷ A (λ x → pop (f x)) (λ x → top (f x)) γ

-- The proofs of AP₀ and AP₁ imply that they should hold
-- definitionally for all concrete telescopes.  Thus, it is reasonable
-- to assert them as rewrite rules for all telescopens.  Note that
-- they have a volatile LHS, which reduces on concrete or
-- partially-concrete telescopes; but their definitions make them
-- consistent with such reductions.  Thus, they hold definitionally
-- for partially-concrete telescopes as well.
{-# REWRITE AP₀ AP₁ #-}

-- Since AP₀ and AP₁ hold definitionally on abstract telescopes
-- (at least), we can also prove by UIP that they are equal to reflexivity.
AP₀-reflᵉ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → AP₀ f γ ≡ reflᵉ
AP₀-reflᵉ f γ = axiomK

AP₁-reflᵉ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → AP₁ f γ ≡ reflᵉ
AP₁-reflᵉ f γ = axiomK

-- If we now declare these proofs also as rewrites, then the coercions
-- along AP₀ and AP₁ that we had to insert in the type of Id′-AP and
-- the definition of AP to make them well-typed will disappear.  I
-- think/hope that this won't produce any ill-typed terms, since as
-- noted above AP₀ and AP₁ should hold definitionally on concrete and
-- partially-concrete telescopes and terms too.
{-# REWRITE AP₀-reflᵉ AP₁-reflᵉ #-}

-- A useful derived rule for combining the admissible equality Id′-AP
-- with an equality of base identifications and heterogeneous
-- equalities of the endpoints.
Id′-AP≡ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (δ : el (ID Δ)) (e : δ ≡ AP f γ)
    (A : el Δ → Type) {a₀ : A (f (γ ₀))} {a₁ : A (f (γ ₁))} {b₀ : A (δ ₀)} {b₁ : A (δ ₁)}
    (e₀ : a₀ ≡ʰ b₀) (e₁ : a₁ ≡ʰ b₁) →
    Id′ (λ w → A (f w)) γ a₀ a₁ ≡ Id′ A δ b₀ b₁
Id′-AP≡ f γ .(AP f γ) reflᵉ A {a₀} {a₁} {b₀} {b₁} e₀ e₁ =
  Id′-AP f γ A a₀ a₁ • cong2 (Id′ A (AP f γ)) (≡ʰ→≡ e₀) (≡ʰ→≡ e₁)

-- Functoriality for ap should be admissible, like Id′-AP.
-- However, like ap, it should compute on terms, not types.
postulate
  ap-AP : {Γ Δ : Tel} {A : el Δ → Type} (f : el Γ → el Δ) (g : (x : el Δ) → A x) (γ : el (ID Γ)) →
    ap g (AP f γ) ≡ coe→ (Id′-AP f γ A (g (f (γ ₀))) (g (f (γ ₁)))) (ap (λ w → g (f w)) γ) 

-- From this we can prove the analogous functoriality property for AP,
-- with some awful wrangling of heterogeneous exo-equality.
AP-AP : {Γ Δ Θ : Tel} (f : el Γ → el Δ) (g : el Δ → el Θ) (γ : el (ID Γ)) →
  AP g (AP f γ) ≡ AP (λ w → g (f w)) γ

-- The proof requires a helper lemma for ∷, just like AP₀ and AP₁.
AP-AP-∷ : {Γ Δ Θ : Tel} (A : el Θ → Type) (f : el Γ → el Δ)
  (g : el Δ → el Θ) (h : (x : el Δ) → A (g x)) (γ : el (ID Γ)) →
  AP (λ x → g x ∷ h x) (AP f γ) ≡ AP (λ w → g (f w) ∷ h (f w)) γ
AP-AP-∷ A f g h γ =
      ∷≡ (λ δaa → Id′ A (pop (pop δaa)) (top (pop δaa)) (top δaa))
      (∷≡ (λ δa → A ((pop δa)₁))
           (∷≡ (λ δ → A (δ ₀))
                (AP-AP f g γ)
                reflʰ)
           reflʰ)
       (coe→≡ʰ (Id′-AP g (AP f γ) A (h (f (γ ₀))) (h (f (γ ₁)))) _ •ʰ
       (≡→≡ʰ (ap-AP f h γ) •ʰ
       (coe→≡ʰ (Id′-AP f γ (λ z → A (g z)) (h (f (γ ₀))) (h (f (γ ₁)))) _ •ʰ
        revʰ (coe→≡ʰ (Id′-AP (λ x → g (f x)) γ A (h (f (γ ₀))) (h (f (γ ₁)))) _))))

AP-AP {Θ = ε} f g γ = reflᵉ
AP-AP {Γ} {Δ} {Θ ▸ A} f g γ = AP-AP-∷ A f (λ x → pop (g x)) (λ x → top (g x)) γ

-- Inspecting the above definition, we see that on a concrete
-- telescope, AP-AP consists essentially of reflexivities on points
-- and complex combinations of Id′-AP and ap-AP on identifications.
-- Thus, if the types and terms are also concrete, it should reduce
-- away to reflexivity too.

-- Now, since we defined AP to compute only on ∷ rather than just ▸,
-- we can also make it compute on top and pop.

postulate
  AP-pop : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    AP (λ x → pop (f x)) γ ≡ pop (pop (pop (AP f γ)))

{-# REWRITE AP-pop #-}

-- We can also prove that all the pieces of the original ▸-only
-- definition hold.  In fact, we need to do this before we can assert
-- that AP computes on top.

top-pop-pop-AP : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
  top (pop (pop (AP f γ))) ≡ coe← (cong A (AP₀ (λ x → pop (f x)) γ)) (top (f (γ ₀)))

top-pop-pop-AP-∷ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el Δ) (g : (x : el Γ) → A (f x)) (γ : el (ID Γ)) →
  top (pop (pop (AP {Δ = Δ ▸ A} (λ x → f x ∷ g x) γ))) ≡ coe← (cong A (AP₀ f γ)) (g (γ ₀))
top-pop-pop-AP-∷ A f g γ = reflᵉ

top-pop-pop-AP A f γ = top-pop-pop-AP-∷ A (λ x → pop (f x)) (λ x → top (f x)) γ

top-pop-AP : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
  top (pop (AP f γ)) ≡ coe← (cong A (AP₁ (λ x → pop (f x)) γ)) (top (f (γ ₁)))

top-pop-AP-∷ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el Δ) (g : (x : el Γ) → A (f x)) (γ : el (ID Γ)) →
  top (pop (AP {Δ = Δ ▸ A} (λ x → f x ∷ g x) γ)) ≡ coe← (cong A (AP₁ f γ)) (g (γ ₁))
top-pop-AP-∷ A f g γ = reflᵉ

top-pop-AP A f γ = top-pop-AP-∷ A (λ x → pop (f x)) (λ x → top (f x)) γ

postulate
  ap-top : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    ap (λ x → top (f x)) γ ≡
    coe← (Id′-AP (λ x → pop (f x)) γ A (top (f (γ ₀))) (top (f (γ ₁))))
      (coe→ (cong2 (Id′ A (pop (pop (pop (AP f γ))))) (top-pop-pop-AP A f γ) (top-pop-AP A f γ))
        (top (AP f γ)))

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

-- Combining ap-top and AP-pop with AP on the identity, we will be
-- able to compute ap on any (De Bruijn) variable.  It may seem like
-- this should be provable at this point, but I don't think it is.
postulate
  AP-idmap : {Δ : Tel} (δ : el (ID Δ)) → AP {Δ} {Δ} (λ w → w) δ ≡ δ

{-# REWRITE AP-idmap #-}

-- However, we can make it reduce away on endpoints.
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

{-
top-pop-pop-AP-idmap : {Δ : Tel} (A : el Δ → Type) (γ : el (ID (Δ ▸ A))) →
  top-pop-pop-AP A (λ x → x) γ ≡ reflᵉ
top-pop-pop-AP-idmap A γ = axiomK

top-pop-AP-idmap : {Δ : Tel} (A : el Δ → Type) (γ : el (ID (Δ ▸ A))) →
  top-pop-AP A (λ x → x) γ ≡ reflᵉ
top-pop-AP-idmap A γ = axiomK

top-pop-pop-AP-pop : {Γ Δ : Tel} (A : el Δ → Type) (B : el (Δ ▸ A) → Type) (f : el Γ → el (Δ ▸ A ▸ B)) (γ : el (ID Γ)) →
  top-pop-pop-AP A (λ x → pop (f x)) γ ≡ {!top-pop-pop-AP B f γ!}
top-pop-pop-AP-pop A B γ = {!!}
-}

{-# REWRITE AP-AP-idmap AP-AP-idmap′ Id′-AP-idmap #-}
