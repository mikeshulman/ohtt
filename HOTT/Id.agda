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
infix 10 _₀ _₁

-- They are also mutual with the (postulated) dependent/heterogeneous
-- identity *types* that they are composed of.
postulate
  -- Note that these depend on an element of the bundled (ID Δ), which
  -- consists of two points of Δ and an identification between them.
  Id′ : {Δ : Tel} (A : el Δ → Type) (δ : el (ID Δ)) (a₀ : A (δ ₀)) (a₁ : A (δ ₁)) → Type

ID ε = ε
ID (Δ ▸ A) = ID Δ ▸ (λ δ → A (δ ₀)) ▸ (λ δa → A ((pop δa)₁)) ▸ (λ δaa → Id′ A (pop (pop δaa)) (top (pop δaa)) (top δaa))

_₀ {ε} _ = []
_₀ {Δ ▸ A} δ = ((pop (pop (pop δ)))₀) ∷ top (pop (pop δ))

_₁ {ε} _ = []
_₁ {Δ ▸ A} δ = ((pop (pop (pop δ)))₁) ∷ top (pop δ)

----------------------------------------
-- Telescope ap and functoriality, I
----------------------------------------

postulate
  -- Since Id will be definitionally a special case of Id′, we don't
  -- need separate and non-dependent versions of ap.  Note that like
  -- Id′, it depends on an element of the bundled (ID Δ).
  ap : {Δ : Tel} {A : el Δ → Type} (f : (δ : el Δ) → A δ) (δ : el (ID Δ)) → Id′ A δ (f (δ ₀)) (f (δ ₁))

-- Telescope AP.  I hope we can get away with only the non-dependent version.  We'd like to *define* it by recursion on the target telescope:
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
-- matching inside a λ, so it has to be done with rewrite rules.
postulate
  AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → el (ID Δ)

-- We define this mutually with proofs that its projections are the
-- action of the original f on the projections.
postulate
  AP₀ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → ((AP f γ)₀) ≡ f (γ ₀)
  AP₁ : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) → ((AP f γ)₁) ≡ f (γ ₁)

-- We also define it mutually with postulated naturality for Id′.
-- This rule should be admissible, meaning we will give rewrite rules
-- making it hold definitionally on all concrete telescopes and terms.
-- Specifically, Id′-AP should compute on types, like Id′.
postulate
  Id′-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) (A : el Δ → Type) (a₀ : A (f (γ ₀))) (a₁ : A (f (γ ₁))) →
    Id′ (λ w → A (f w)) γ a₀ a₁ ≡ Id′ A (AP f γ) (coe← (cong A (AP₀ f γ)) a₀) (coe← (cong A (AP₁ f γ)) a₁)

-- In defining AP, we have to coerce along AP₀, AP₁ and Id′-AP.
postulate
  APε : {Γ : Tel} (f : el Γ → el ε) (γ : el (ID Γ)) → AP {Δ = ε} f γ ≡ []
  AP∷ : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el Δ) (A : el Δ → Type) (g : (x : el Γ) → A (f x)) →
    AP {Δ = Δ ▸ A} (λ x → f x ∷ g x) γ ≡
      AP f γ ∷
      coe← (cong A (AP₀ f γ)) (g (γ ₀)) ∷
      coe← (cong A (AP₁ f γ)) (g (γ ₁)) ∷
      coe→ (Id′-AP f γ A (g (γ ₀)) (g (γ ₁))) (ap g γ)

{-# REWRITE APε AP∷ #-}

-- Similarly, AP₀ and AP₁ also have to be "defined" on ∷ by matching inside λ.
postulate
  AP₀ε : {Γ : Tel} (f : el Γ → el ε) (γ : el (ID Γ)) → AP₀ {Δ = ε} f γ ≡ reflᵉ
  AP₀∷ : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el Δ) (A : el Δ → Type) (g : (x : el Γ) → A (f x)) →
    AP₀ {Δ = Δ ▸ A} (λ x → f x ∷ g x) γ ≡
    ∷≡ʰ A (AP₀ f γ) (coe←≡ʰ (cong A (AP₀ f γ)) (g (γ ₀)))
  AP₁ε : {Γ : Tel} (f : el Γ → el ε) (γ : el (ID Γ)) → AP₁ {Δ = ε} f γ ≡ reflᵉ
  AP₁∷ : {Γ Δ : Tel} (γ : el (ID Γ)) (f : el Γ → el Δ) (A : el Δ → Type) (g : (x : el Γ) → A (f x)) →
    AP₁ {Δ = Δ ▸ A} (λ x → f x ∷ g x) γ ≡
    ∷≡ʰ A (AP₁ f γ) (coe←≡ʰ (cong A (AP₁ f γ)) (g (γ ₁)))

{-# REWRITE AP₀ε AP₀∷ AP₁ε AP₁∷ #-}

-- The proofs of AP₀ and AP₁ imply that they should hold
-- definitionally for all concrete terms.  Thus, it is reasonable to
-- assert them as rewrite rules for all terms.  Note that they have a
-- volatile LHS, which reduces on concrete or partially-concrete
-- contexts and terms, but they are consistent with such reductions by
-- the definitions of AP₀ and AP₁.  Thus, AP₀ and AP₁ hold
-- definitionally for partially-concrete contexts/terms as well.
{-# REWRITE AP₀ AP₁ #-}

-- Since AP₀ and AP₁ hold definitionally on abstract contexts/terms
-- (at least), we can prove by UIP that they are equal to reflexivity.
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

-- Functoriality for ap should also be admissible, like Id′-AP.
-- However, like ap, it should compute on terms, not types.
postulate
  ap-AP : {Γ Δ : Tel} (f : el Γ → el Δ) (γ : el (ID Γ)) {A : el Δ → Type} (g : (x : el Δ) → A x) →
    ap g (AP f γ) ≡ coe→ (Id′-AP f γ A (g (f (γ ₀))) (g (f (γ ₁)))) (ap (λ w → g (f w)) γ) 

-- From this we can "prove" the analogous functoriality property for AP,
-- with some awful wrangling of heterogeneous exo-equality.
postulate
  AP-AP : {Γ Δ Θ : Tel} (f : el Γ → el Δ) (g : el Δ → el Θ) (γ : el (ID Γ)) →
    AP g (AP f γ) ≡ AP (λ w → g (f w)) γ
  AP-AP-ε : {Γ Δ : Tel} (f : el Γ → el Δ) (g : el Δ → el ε) (γ : el (ID Γ)) →
    AP-AP {Θ = ε} f g γ ≡ reflᵉ
  AP-AP-∷ : {Γ Δ Θ : Tel} (f : el Γ → el Δ) (g : el Δ → el Θ) (γ : el (ID Γ))
    (A : el Θ → Type) (h : (x : el Δ) → A (g x)) →
    AP-AP {Γ} {Δ} {Θ ▸ A} f (λ x → g x ∷ h x) γ ≡
      ∷≡ʰ (λ δaa → Id′ A (pop (pop δaa)) (top (pop δaa)) (top δaa))
      (∷≡ʰ (λ δa → A ((pop δa)₁))
           (∷≡ʰ (λ δ → A (δ ₀))
                (AP-AP f g γ)
                reflʰ)
           reflʰ)
       (coe→≡ʰ (Id′-AP g (AP f γ) A (h (f (γ ₀))) (h (f (γ ₁)))) _ •ʰ
       (≡→≡ʰ (ap-AP f γ h) •ʰ
       (coe→≡ʰ (Id′-AP f γ (λ z → A (g z)) (h (f (γ ₀))) (h (f (γ ₁)))) _ •ʰ
        revʰ (coe→≡ʰ (Id′-AP (λ x → g (f x)) γ A (h (f (γ ₀))) (h (f (γ ₁)))) _))))
-- Inspecting this definition, we see that on a concrete telescope,
-- AP-AP consists essentially of reflexivities on points and complex
-- combinations of Id′-AP and ap-AP on identifications.  Thus, if the
-- types and terms are also concrete, it should reduce away to
-- reflexivity too.

{-# REWRITE AP-AP-ε AP-AP-∷ #-}

-- Since we "defined" AP and AP-AP to compute only on ∷ rather than
-- just ▸, we can also make them compute on top and pop.  More
-- generally, we can "prove" that all the pieces of the original
-- ▸-only definition hold.

postulate
  AP-pop : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    AP (λ x → pop (f x)) γ ≡ pop (pop (pop (AP f γ)))

{-# REWRITE AP-pop #-}

-- Unfortunately, these can't be rewrite rules, but we can make them
-- reduce on ∷.
postulate
  top-pop-pop-AP : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (pop (AP f γ))) ≡ coe← (cong A (AP₀ (λ x → pop (f x)) γ)) (top (f (γ ₀)))
  top-pop-AP : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    top (pop (AP f γ)) ≡ coe← (cong A (AP₁ (λ x → pop (f x)) γ)) (top (f (γ ₁)))
  top-pop-pop-AP-∷ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el Δ) (g : (x : el Γ) → A (f x)) (γ : el (ID Γ)) →
    top-pop-pop-AP A (λ x → f x ∷ g x) γ ≡ reflᵉ
  top-pop-AP-∷ : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el Δ) (g : (x : el Γ) → A (f x)) (γ : el (ID Γ)) →
    top-pop-AP A (λ x → f x ∷ g x) γ ≡ reflᵉ

{-# REWRITE top-pop-pop-AP-∷ top-pop-AP-∷ #-}

postulate
  ap-top : {Γ Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) (γ : el (ID Γ)) →
    ap (λ x → top (f x)) γ ≡
    coe← (Id′-AP (λ x → pop (f x)) γ A (top (f (γ ₀))) (top (f (γ ₁))))
      (coe→ (cong2 (Id′ A (pop (pop (pop (AP f γ))))) (top-pop-pop-AP A f γ) (top-pop-AP A f γ))
        (top (AP f γ)))

{-# REWRITE ap-top #-}

-- Note that we don't have rules for computing ap-top on "dependent
-- telescopes".  Hopefully this won't ever occur.

-- Combining ap-top and AP-pop with AP on the identity, we will be
-- able to compute ap on any (De Bruijn) variable.
postulate
  AP-idmap : {Δ : Tel} (δ : el (ID Δ)) → AP {Δ} {Δ} (λ w → w) δ ≡ δ

{-# REWRITE AP-idmap #-}

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

-- TODO: Left off porting

{-
------------------------------
-- Computing with ap
------------------------------

-- AP and AP′ are "defined" to be lists of ap.  It's tempting to make
-- them compute based on the target *telescope*, i.e. AP into a ▸
-- computes to a ∷, AP into a ► computes to a PAIR, like this:
{-
postulate
  APε : {Θ : Tel} (f : el Θ → el ε) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → AP {Θ} f t₂ ≡ []
  AP▸ : {Θ Δ : Tel} (A : el Δ → Type) (f : el Θ → el (Δ ▸ A)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP {Θ} {Δ ▸ A} f t₂ ≡ AP {Θ} {Δ} (λ w → pop (f w)) t₂ ∷ coe→ (Id-AP (λ w → pop (f w)) t₂ A (top (f t₀)) (top (f t₁)))
                                                                   (ap (λ w → top (f w)) t₂)
  AP► : {Γ Δ : Tel} (Θ : el Δ → Tel) (f : el Γ → el (Δ ► Θ)) {γ₀ γ₁ : el Γ} (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP {Γ} {Δ ► Θ} f γ₂ ≡ PAIR (λ e → ID′ Θ e (TOP Θ (f γ₀)) (TOP Θ (f γ₁)))
                             (AP {Γ} {Δ} (λ w → POP Θ (f w)) γ₂)
                             (COE← (ID-AP (λ w → POP Θ (f w)) γ₂ Θ (TOP Θ (f γ₀)) (TOP Θ (f γ₁)))
                               (AP′ {Γ} (λ w → Θ (POP Θ (f w))) (λ w → TOP Θ (f w)) γ₂)) 

{-# REWRITE APε AP▸ AP► #-}

postulate
  AP′ε : {Θ : Tel} (f : (x : el Θ) → el ε) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP′ {Θ} (λ _ → ε) f t₂ ≡ []
  AP′▸ : {Θ : Tel} (Δ : el Θ → Tel) (A : (x : el Θ) → el (Δ x) → Type) (f : (x : el Θ) → el (Δ x ▸ A x))
    {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP′ {Θ} (λ w → Δ w ▸ A w) f t₂ ≡
    AP′ {Θ} Δ (λ w → pop (f w)) t₂ ∷
      coe→ (Id-AP (λ w → PAIR Δ w (pop (f w))) t₂ (λ w → A (POP Δ w) (TOP Δ w)) (top (f t₀)) (top (f t₁)))
           (ap (λ w → top (f w)) t₂)
  AP′► : {Θ : Tel} (Δ : el Θ → Tel) (Γ : (x : el Θ) → el (Δ x) → Tel) (f : (x : el Θ) → el (Δ x ► Γ x))
    {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP′ {Θ} (λ w → Δ w ► Γ w) f t₂ ≡
    PAIR (λ γ₂ → ID′ (UNCURRY Δ Γ) (PAIR (λ w → ID′ Δ w (POP (Γ t₀) (f t₀)) (POP (Γ t₁) (f t₁))) t₂ γ₂)
                     (TOP (Γ t₀) (f t₀)) (TOP (Γ t₁) (f t₁)))
         (AP′ {Θ} Δ (λ w → POP (Γ w) (f w)) t₂)
         (COE← (ID-AP (λ w → PAIR Δ w (POP (Γ w) (f w))) t₂ (UNCURRY Δ Γ) (TOP (Γ t₀) (f t₀)) (TOP (Γ t₁) (f t₁)))
           (AP′ (λ w → Γ w (POP (Γ w) (f w))) (λ w → TOP (Γ w) (f w)) t₂))

{-# REWRITE AP′ε AP′▸ AP′► #-}
-}
-- However, we also need to deal with AP on things like pop, POP, and
-- TOP, and if we also gave rules for those, the result would be
-- circular.  Thus, we instead follow the lead of ap into a Σ-type,
-- which computes only on an actual pair _,_, and define AP and AP′ to
-- compute only on the *terms* ∷ and PAIR.  Pleasingly, the terms we
-- get here are shorter too.

postulate
  AP[] : {Θ : Tel} {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → AP {Θ} (λ _ → []) t₂ ≡ []
  AP∷ : {Θ Δ : Tel} (A : el Δ → Type) (f : el Θ → el Δ) (g : (t : el Θ) → A (f t)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP (λ t → f t ∷ g t) t₂ ≡ AP f t₂ ∷ coe← (Id′-AP f t₂ A (g t₀) (g t₁)) (ap g t₂)
  AP-PAIR : {Γ Δ : Tel} (Θ : el Δ → Tel) (f : el Γ → el Δ) (g : (γ : el Γ) → el (Θ (f γ))) {γ₀ γ₁ : el Γ} (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP (λ t → PAIR Θ (f t) (g t)) γ₂ ≡
    PAIR (λ e → ID′ Θ e (g γ₀) (g γ₁)) (AP f γ₂) (COE← (ID′-AP f γ₂ Θ (g γ₀) (g γ₁)) (AP′ (λ w → Θ (f w)) g γ₂))

{-# REWRITE AP[] AP∷ AP-PAIR #-}

postulate
  -- AP′[] would follow from AP[] and AP′-CONST
  AP′[] : {Θ : Tel} {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → AP′ {Θ} (λ _ → ε) (λ _ → []) t₂ ≡ []
  AP′∷ : {Θ : Tel} (Δ : el Θ → Tel) (A : (x : el Θ) → el (Δ x) → Type)
    (f : (x : el Θ) → el (Δ x)) (g : (x : el Θ) → A x (f x)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP′ (λ w → Δ w ▸ A w) (λ w → f w ∷ g w) t₂ ≡
    AP′ Δ f t₂ ∷ coe← (Id′-AP (λ w → PAIR Δ w (f w)) t₂ (UNCURRY Δ A) (g t₀) (g t₁)) (ap g t₂)
  AP′-PAIR : {Θ : Tel} (Δ : el Θ → Tel) (Γ : (x : el Θ) → el (Δ x) → Tel)
    (f : (x : el Θ) → el (Δ x)) (g : (x : el Θ) → el (Γ x (f x))) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP′ (λ w → Δ w ► Γ w) (λ w → PAIR (Γ w) (f w) (g w)) t₂ ≡
    PAIR (λ γ₂ → ID′ (UNCURRY Δ Γ) (PAIR (λ w → ID′ Δ w (f t₀) (f t₁)) t₂ γ₂) (g t₀) (g t₁))
         (AP′ Δ f t₂)
         (COE← (ID′-AP (λ w → PAIR Δ w (f w)) t₂ (UNCURRY Δ Γ) (g t₀) (g t₁)) (AP′ (λ w → Γ w (f w)) g t₂))

{-# REWRITE AP′[] AP′∷ AP′-PAIR #-}

postulate
  AP-pop : {Γ : Tel} {Δ : Tel} (A : el Δ → Type) (f : el Γ → el (Δ ▸ A)) {γ₀ γ₁ : el Γ} (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP (λ w → pop (f w)) γ₂ ≡ pop (AP f γ₂)
  AP-POP : {Γ : Tel} {Δ : Tel} (Θ : el Δ → Tel) (f : el Γ → el (Δ ► Θ)) (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP (λ w → POP Θ (f w)) γ₂ ≡
    POP (λ w₂ → ID′ Θ w₂ (TOP Θ (f γ₀)) (TOP Θ (f γ₁))) (AP f γ₂)
  AP′-pop : {Γ : Tel} {Δ : el Γ → Tel} (A : (x : el Γ) → el (Δ x) → Type) (f : (x : el Γ) → el (Δ x ▸ A x))
            {γ₀ γ₁ : el Γ} (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP′ Δ (λ w → pop (f w)) γ₂ ≡
      pop {ID′ Δ γ₂ (pop (f γ₀)) (pop (f γ₁))}
          {λ t₂ → Id′ (UNCURRY Δ A) (PAIR (λ w → ID′ Δ w (pop (f γ₀)) (pop (f γ₁))) γ₂ t₂) (top (f γ₀)) (top (f γ₁))}
          (AP′ (λ w → Δ w ▸ A w) f γ₂)
  AP′-POP : {Γ : Tel} {Δ : el Γ → Tel} (Θ : (x : el Γ) → el (Δ x) → Tel) (f : (x : el Γ) → el (Δ x ► Θ x))
           (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP′ Δ (λ w → POP (Θ w) (f w)) γ₂ ≡
    POP (λ t₂ → ID′ (UNCURRY Δ Θ) (PAIR (λ w → ID′ Δ w (POP (Θ γ₀) (f γ₀)) (POP (Θ γ₁) (f γ₁))) γ₂ t₂)
          (TOP (Θ γ₀) (f γ₀)) (TOP (Θ γ₁) (f γ₁)))
        (AP′ (λ x → Δ x ► Θ x) f γ₂)

{-# REWRITE AP-pop AP-POP AP′-pop AP′-POP #-}

postulate
  AP-TOP : {Γ : Tel} {Δ : Tel} (Θ : Tel) (f : el Γ → el (PROD Δ Θ)) (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP (λ w → TOP (λ _ → Θ) (f w)) γ₂ ≡
    COE→ (ID′-CONST Θ _ _ _)
          (TOP (λ w₂ → ID′ (λ _ → Θ) w₂ (SND Δ Θ (f γ₀)) (SND Δ Θ (f γ₁))) (AP f γ₂)) 
  --- This is a weaker version of AP′-TOP, into a partially constant family
  -- AP′-TOP : {Γ : Tel} {Δ : Tel} (Θ : el Δ → Tel) (f : el Γ → el (Δ ► Θ)) (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁)) →
  --   AP′ (λ w → Θ (POP Θ (f w))) (λ w → TOP Θ (f w)) γ₂ ≡
  --   COE→ (ID-AP (λ w → POP Θ (f w)) γ₂ Θ (TOP Θ (f γ₀)) (TOP Θ (f γ₁)))
  --         (TOP (λ w₂ → ID′ Θ w₂ (TOP Θ (f γ₀)) (TOP Θ (f γ₁))) (AP f γ₂))
  AP′-TOP : {Γ : Tel} {Δ : el Γ → Tel} (Θ : (x : el Γ) → el (Δ x) → Tel) (f : (x : el Γ) → el (Δ x ► Θ x))
            (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁)) →
    AP′ (λ w → Θ w (POP (Θ w) (f w))) (λ w → TOP (Θ w) (f w)) γ₂ ≡
    COE→ (ID′-AP′ Δ (λ w → POP (Θ w) (f w)) γ₂ Θ (TOP (Θ γ₀) (f γ₀)) (TOP (Θ γ₁) (f γ₁)))
          (TOP (λ t₂ → ID′ (UNCURRY Δ Θ) (PAIR (λ w → ID′ Δ w (POP (Θ γ₀) (f γ₀)) (POP (Θ γ₁) (f γ₁))) γ₂ t₂)
                           (TOP (Θ γ₀) (f γ₀)) (TOP (Θ γ₁) (f γ₁)))
               (AP′ (λ x → Δ x ► Θ x) f γ₂))
  -- Since we have AP′-CONST, the dependent ap-top should subsume the non-dependent case.
  ap-top : {Γ : Tel} (Δ : el Γ → Tel) (A : (x : el Γ) → el (Δ x) → Type) (f : (x : el Γ) → el (Δ x ▸ A x))
           (γ₀ γ₁ : el Γ) (γ₂ : el (ID Γ γ₀ γ₁)) →
    ap (λ w → top (f w)) γ₂ ≡
    coe→ (Id′-AP (λ w → PAIR Δ w (pop (f w))) γ₂ (UNCURRY Δ A) (top (f γ₀)) (top (f γ₁)))
         (top (AP′ {Γ} (λ x → Δ x ▸ A x) f γ₂))

{-# REWRITE AP-TOP AP′-TOP ap-top #-}

-}



------------------------------
-- Homogeneous Id and refl
------------------------------

-- Homogeneous identity types are heterogeneous over the empty
-- telescope.  However, if we *defined* them to be that:
{-
Id : (A : Type) → A → A → Type
Id A a₀ a₁ = Id′ {Δ = ε} (λ _ → A) [] a₀ a₁
-}
-- then we couldn't rewrite Id′ of an arbitrary *constant* type family
-- to Id without producing infinite loops, since the above is also a
-- particular constant type family.  So instead we postulate Id
-- separately, along with the reduction for constant type families,
-- which has as a particular consequence that the above definitional
-- equality also holds.

postulate
  Id : (A : Type) → A → A → Type
  Id-const : {Δ : Tel} (A : Type) (δ : el (ID Δ)) (a₀ a₁ : A) →
    Id′ {Δ} (λ _ → A) δ a₀ a₁ ≡ Id A a₀ a₁

{-# REWRITE Id-const #-}

-- Similarly, reflexivity is nullary ap, with the same caveat.
postulate
  refl : {A : Type} (a : A) → Id A a a
  ap-const : {Δ : Tel} (A : Type) (δ : el (ID Δ)) (a : A) →
    ap {Δ} (λ _ → a) δ ≡ refl a

{-# REWRITE ap-const #-}

-- Now we can define reflexivity for telescopes.
REFL : {Δ : Tel} (δ : el Δ) → el (ID Δ)

-- Like AP, we need to simultaneously prove that it respects ₀ and ₁
REFL₀ : {Δ : Tel} (δ : el Δ) → ((REFL δ)₀) ≡ δ
REFL₁ : {Δ : Tel} (δ : el Δ) → ((REFL δ)₁) ≡ δ

-- Moreover, in order to define REFL we'll also need to know its
-- analogue of Id′-AP, which in this case is something we can prove.
Id′-REFL : {Δ : Tel} (A : el Δ → Type) (δ : el Δ) (a₀ : A ((REFL δ)₀)) (a₁ : A ((REFL δ)₁)) →
  Id′ A (REFL δ) a₀ a₁ ≡
  Id (A δ) (coe→ (cong A (REFL₀ δ)) a₀) (coe→ (cong A (REFL₁ δ)) a₁)

-- But in order to prove *that*, we'll also need to know that REFL is
-- the image of AP on constant terms.
AP-const : {Δ : Tel} (Θ : Tel) (δ : el (ID Δ)) (t : el Θ) →
  AP {Δ} (λ _ → t) δ ≡ REFL t

Id′-REFL {Δ} A δ a₀ a₁ = rev (Id′-AP≡ {ε} (λ _ → δ) [] (REFL δ) (rev (AP-const Δ [] δ)) A
                                      (coe→≡ʰ (cong A (REFL₀ δ)) a₀) ((coe→≡ʰ (cong A (REFL₁ δ)) a₁)))

-- A useful extended version of Id′-REFL, like Id′-AP≡.
Id′-REFL≡ : {Δ : Tel} (A : el Δ → Type) (δ : el Δ)
  {a₀ : A ((REFL δ)₀)} {a₁ : A ((REFL δ)₁)} {b₀ b₁ : A δ} (e₀ : a₀ ≡ʰ b₀) (e₁ : a₁ ≡ʰ b₁) →
  Id′ A (REFL δ) a₀ a₁ ≡ Id (A δ) b₀ b₁
Id′-REFL≡ {Δ} A δ e₀ e₁ = rev (Id′-AP≡ {ε} (λ _ → δ) [] (REFL δ) (rev (AP-const Δ [] δ)) A (revʰ e₀) (revʰ e₁)) 

-- Note that in defining REFL we have to coerce along REFL₀ and REFL₁, and also ID′-REFL≡.
REFL {ε} δ = []
REFL {Δ ▸ A} δ = REFL (pop δ) ∷
                 coe← (cong A (REFL₀ (pop δ))) (top δ) ∷
                 coe← (cong A (REFL₁ (pop δ))) (top δ) ∷
                 coe← (Id′-REFL≡ A (pop δ) (coe←≡ʰ (cong A (REFL₀ (pop δ))) (top δ)) (coe←≡ʰ (cong A (REFL₁ (pop δ))) (top δ)))
                      (refl (top δ))

REFL₀ {ε} δ = reflᵉ
REFL₀ {Δ ▸ A} δ = ∷≡ʰ A (REFL₀ (pop δ)) (coe←≡ʰ (cong A (REFL₀ (pop δ))) _)

REFL₁ {ε} δ = reflᵉ
REFL₁ {Δ ▸ A} δ = ∷≡ʰ A (REFL₁ (pop δ)) (coe←≡ʰ (cong A (REFL₁ (pop δ))) _)

AP-const {Δ} ε δ t = reflᵉ
AP-const {Δ} (Θ ▸ A) δ t = {!!} -- More heterogeneous equality wrangling

-- Many of these can be made rewrites.
-- {-# REWRITE REFL₀ REFL₁ Id′-REFL AP-const #-}

-- TODO: And once they are, we can make them identities, as for AP above.

{-

postulate
  Id′-AP-constfn : {Θ Δ : Tel} (f : el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (A : el Δ → Type) (a₀ a₁ : A f) →
    Id′-AP {Θ} (λ _ → f) {t₀} {t₁} t₂ A a₀ a₁ ≡ reflᵉ

{-# REWRITE Id′-AP-constfn #-}

-- The usefulness of having Id-REFL as a rewrite is limited in
-- practice, because if δ has internal structure, REFL will compute on
-- it, and can't be "un-rewritten" back to a REFL in order for Id-REFL
-- to fire.  So we still sometimes have to coerce along Id-REFL.
-- However, Id′-AP-constfn above minimizes the effect of these
-- coercions, since they specialize to imply that Id-REFL is
-- reflexivity, so that in situations where it's possible, the
-- coercion gets reduced away.

-- Now we can do the same for ap on REFL.
ap-REFL : {Δ : Tel} (A : el Δ → Type) (f : (δ : el Δ) → A δ) (δ : el Δ) →
  ap f (REFL δ) ≡ refl (f δ)
ap-REFL {Δ} A f δ = ap-AP {ε} (λ _ → δ) [] f  

AP-REFL : {Δ Θ : Tel} (f : el Δ → el Θ) (δ : el Δ) →
  AP f (REFL δ) ≡ REFL (f δ)
AP-REFL f δ = AP-AP {ε} (λ _ → δ) [] f

{-# REWRITE ap-REFL AP-REFL #-}

-- We can now assert that the functoriality rules for constant
-- families and functions reduce to reflexivity, which is well-typed
-- since both sides reduce to a homogeneous Id or a refl.
postulate
  Id′-AP-constty : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (A : Type) (a₀ a₁ : A) →
    Id′-AP f t₂ (λ _ → A) a₀ a₁ ≡ reflᵉ

{-# REWRITE Id′-AP-constty #-}

postulate
  ap-AP-constty : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {A : Type} (g : A) →
    ap-AP f t₂ (λ _ → g) ≡ reflᵉ
  AP-AP-constty : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {Γ : Tel} (g : el Γ) →
    AP-AP f t₂ (λ _ → g) ≡ reflᵉ

{-# REWRITE ap-AP-constty AP-AP-constty #-}

-- The choice not to define Id as an instance of Id′ does mean that
-- all the rewrites we postulate for Id′, ap, and AP have to be given
-- separately for Id, refl, and REFL, in case the former get reduced
-- to the latter before these rules fire.

postulate
  REFL[] : REFL [] ≡ []
  REFL∷ : {Δ : Tel} (A : el Δ → Type) (f : el Δ) (g : A f) →
    REFL {Δ ▸ A} (f ∷ g) ≡ REFL f ∷ coe← (Id-REFL A f g g) (refl g)
  REFL-PAIR : {Δ : Tel} (Θ : el Δ → Tel) (f : el Δ) (g : el (Θ f)) →
    REFL (PAIR Θ f g) ≡ PAIR (λ w₂ → ID′ Θ w₂ g g) (REFL f) (COE← (ID′-AP {ε} (λ _ → f) [] Θ g g) (REFL g))

{-# REWRITE REFL[] REFL∷ REFL-PAIR #-}

postulate
  REFL-pop : {Δ : Tel} (A : el Δ → Type) (f : el (Δ ▸ A)) →
    REFL (pop f) ≡ pop (REFL f)
  REFL-POP : {Δ : Tel} (Θ : el Δ → Tel) (f : el (Δ ► Θ)) →
    REFL (POP Θ f) ≡ POP (λ w₂ → ID′ Θ w₂ (TOP Θ f) (TOP Θ f)) (REFL f)

{-# REWRITE REFL-pop REFL-POP #-}

postulate
  REFL-TOP : {Δ : Tel} (Θ : el Δ → Tel) (f : el (Δ ► Θ)) →
    REFL (TOP Θ f) ≡
    COE→ (ID′-AP {ε} (λ _ → POP Θ f) [] Θ (TOP Θ f) (TOP Θ f))
          (TOP (λ w₂ → ID′ Θ w₂ (TOP Θ f) (TOP Θ f)) (REFL f))
  refl-top : (Δ : Tel) (A : el Δ → Type) (f : el (Δ ▸ A)) →
    refl (top f) ≡ coe→ (Id′-AP {ε} (λ _ → pop f) [] A (top f) (top f)) (top (REFL f)) 

-}
