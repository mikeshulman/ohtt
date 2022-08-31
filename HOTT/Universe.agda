{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Universe where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Exonat
open import HOTT.Cube

infix 30 _↓

------------------------------
-- Bitotal correspondences
------------------------------

-- Morally, the definition of bitotal correspondence should be
{-
（ tr⇒ ⦂ A ⇒ B ）× （ tr⇐ ⦂ B ⇒ A ）× （ rel ⦂ A ⇒ B ⇒ Type ）×
  (（ x ⦂ A ）⇒ rel ∙ x ∙ (tr⇒ ∙ x)) × ( （ y ⦂ B ）⇒ rel ∙ (tr⇐ ∙ y) ∙ y)
-}
-- However, nested Σ-types seem to make Agda really slow, possibly
-- because our Σ-types were postulates and so all the parameters had
-- to be carried around as implicit arguments to fst, snd, and _,_.
-- Thus, instead we define bitotal correspondences to be a datatype.
-- (We can't make it a record for the same reason as Σ.)

-- (TODO: Is this still true now that we've made Σ a datatype?  Could
-- we go back to using a Σ-type here?)

-- As a mnemonic, whenever a coercion- or transport-like operation
-- belongs to a ⇒, so that it has to be applied with ∙, we name it
-- with a ⇒ or a ⇐.

data _≊_ (A B : Type) : Type where
  ≊[_,_,_,_,_] :
    (rel : A ⇒ B ⇒ Type) →
    (coe⇒ : A ⇒ B) →
    (coe⇐ : B ⇒ A) →
    (（ a ⦂ A ）⇒ rel ∙ a ∙ (coe⇒ ∙ a)) →
    (（ b ⦂ B ）⇒ rel ∙ (coe⇐ ∙ b) ∙ b) →
    A ≊ B
open _≊_ public

_／_～_ : {A B : Type} (e : A ≊ B) → A → B → Type
≊[ rel , _ , _ , _ , _ ] ／ a ～ b = rel ∙ a ∙ b

coe⇒ : {A B : Type} (e : A ≊ B) → A ⇒ B
coe⇒ ≊[ rel , coe⇒ , coe⇐ , _ , _ ] = coe⇒

coe⇐ : {A B : Type} (e : A ≊ B) → B ⇒ A
coe⇐ ≊[ rel , coe⇒ , coe⇐ , _ , _ ] = coe⇐

push⇒ : {A B : Type} (e : A ≊ B) → （ a ⦂ A ）⇒ (e ／ a ～ (coe⇒ e ∙ a))
push⇒ ≊[ rel , coe⇒ , coe⇐ , push⇒ , push⇐ ] = push⇒

push⇐ : {A B : Type} (e : A ≊ B) → （ b ⦂ B ）⇒ (e ／ (coe⇐ e ∙ b) ～ b)
push⇐ ≊[ rel , coe⇒ , coe⇐ , push⇒ , push⇐ ] = push⇐

[≊] : (X₀ X₁ : Type) (X₂ : X₀ ＝ X₁) → Type
[≊] X₀ X₁ X₂ = X₀ ≊ X₁

-- This means that the rules for computing ＝, Id, tr⇒, etc. in
-- Σ-types don't apply to _≊_, so for the theory to be complete, we'll
-- need to give separate rules for it.  Perhaps we can compute those
-- to the nested Σ-type that they would have been if it were a nested
-- Σ-type.  Or, if we'll need to actually use them in practice, maybe
-- we should make them a record too, and only go to Σ-types at the
-- next level.

------------------------------
-- Kan cubical structure
------------------------------

-- One way to describe the Kan cubical structure is with a √-type:
{-
postulate
  √ : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) → I → Type
  dig : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type} {i₀ i₁ : I} {i₂ : i₀ ＝ i₁}
    {s₀ : √ A i₀} {s₁ : √ A i₁} (s₂ : Id (√ A) i₂ s₀ s₁) →
    A i₀ i₁ i₂
  bury : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) {@♭ K : Type} (@♭ j : K → I)
    (@♭ d : (k₀ k₁ : K) (k₂ : k₀ ＝ k₁) → A (j k₀) (j k₁) (ap j k₂)) →
    (k : K) → √ A (j k)
-}
-- With identities defined like so:
{-
√′-I : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) → Type
√′-I {I} A = （ i₀ ⦂ I ）× （ i₁ ⦂ I ）× （ i₂ ⦂ i₀ ＝ i₁ ）× √ A i₀ × √ A i₁

√′-A : {@♭ I : Type} (@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type) →
  (u₀ u₁ : √′-I A) (u₂ : u₀ ＝ u₁) → Type
√′-A {I} A u₀ u₁ u₂ =
  Id {ID I} (λ iₓ → A (₁st iₓ) (₂nd iₓ) (₃rd' iₓ))
    {₁st u₀ , ₁st u₁ , ₁st u₂} {₂nd u₀ , ₂nd u₁ , ₂nd u₂}
    -- NB: There is a symmetry here!
    (₃rd u₀ , ₃rd u₁ , sym I ┌─     ₂nd u₂     ─┐
                             ₃rd u₀   □    ₃rd u₁
                             └─     ₁st u₂     ─┘  (₃rd u₂))
    (dig {I} {A} {₁st u₀} {₁st u₁} {₁st u₂} {₄th u₀} {₄th u₁}
         (←Id-ap {（ z ⦂ I × I ）× fst z ＝ snd z} {I} (λ z → fst (fst z)) (𝛌 (√ A))
                 {(₁st u₀ , ₂nd u₀) , ₃rd u₀} {(₁st u₁ , ₂nd u₁) , ₃rd u₁} ((₁st u₂ , ₂nd u₂) , ₃rd u₂)
                 (₄th u₂)))
    (dig {I} {A} {₂nd u₀} {₂nd u₁} {₂nd u₂} {₅th' u₀} {₅th' u₁}
         (←Id-ap {（ w ⦂ （ z ⦂ I × I ）× fst z ＝ snd z ）× √ A (fst (fst w))} {I} (λ z → snd (fst (fst z))) (𝛌 (√ A))
                 {((₁st u₀ , ₂nd u₀) , ₃rd u₀) , ₄th u₀} {((₁st u₁ , ₂nd u₁) , ₃rd u₁) , ₄th u₁} (((₁st u₂ , ₂nd u₂) , ₃rd u₂) , ₄th u₂)
                 (₅th' u₂)))

postulate
  ＝-√ : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type} (i : I) (s₀ s₁ : √ A i) →
    (s₀ ＝ s₁) ≡
    A i i (refl i) × √ {√′-I A} (√′-A A) (i , i , refl i , s₀ , s₁)
  Id-√ : {@♭ I : Type} {@♭ A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Type}
    {Δ : Type} (i : Δ → I) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (s₀ : √ A (i δ₀)) (s₁ : √ A (i δ₁)) →
    Id (λ δ → √ A (i δ)) δ₂ s₀ s₁ ≡
    A (i δ₀) (i δ₁) (ap i δ₂) × √ {√′-I A} (√′-A A) (i δ₀ , i δ₁ , ap i δ₂ , s₀ , s₁)
{-# REWRITE ＝-√ Id-√ #-}
-}
-- Then dig can be identified with fst, we can compute ap-dig to
-- another dig, and so on.  Then the kan structure is given by
{-
postulate
  kan : (X : Type) → √ [≊] X
-}
-- However, computing with √ in practice gets kind of hairy; the naive
-- rules ＝-√ and Id-√ above cause divergence in normalization.  I
-- think the reason is that the base I type of the "√(Id)" includes
-- two points in (√ A) itself, and therefore any occurrence of
-- identifications in that type (such as in the domain of √′-A, when
-- reduced by ＝-Σ) will involve reducing the same Id-√.  I've tried
-- various tricks, but right now the most promising seems to be to
-- "β-reduce away" the √ completely and just assert the resulting
-- destructors of iterated identity types of the universe by hand.

-- To this end, we use a "type of n-cubes in the universe" for all
-- exo-natural numbers n.

-- This is the output type of the Kan structure on n-cubes.
Kan : (n : ℕᵉ) → ∂ n Type ⇒ Type

postulate
  -- Here is the function assigning such structure.  We include an
  -- equality to eliminate green slime in rewrites, notably ap-kan
  -- below which will say that (ap (kan {n})) is part of (kan {𝐬 n}).
  -- The other parts of (kan {𝐬 n}) are determined by symmetry.
  kan : {n : ℕᵉ} (A : CUBE n Type) {Ω : Type} ⦃ ω : Kan n ∙ fst A ≡ Ω ⦄ → Ω
  -- In order to define Kan, recursively on n, we define in parallel a
  -- type of "Kan-generators".  This comes from the type under the √
  -- in the iterated identity types of a √, which on each application
  -- of Id gets copied *outside* the √ but also gets an Id applied to
  -- itself under the √.  It essentially adds one more primitive
  -- symmetry every time we go up a dimension.
  gKan : (n : ℕᵉ) → ∂ (𝐬 n) Type ⇒ Type

Kan 𝐳 = ƛ _ ⇒ ⊤
Kan (𝐬 n) = ƛ A ⇒ Id {∂ n Type} (Kan n ∙_) {A !₀} {A !₁} (A !₂)
                     (kan (A !₀ , A !⁰)) (kan (A !₁ , A !¹)) × gKan n ∙ A

-- gKan is actually defined recursively on ℕᵉ.  But the successor case
-- can't be stated until we have symmetry and more computation laws
-- for ap, so we postpone it by making gKan into a postulate and its
-- definitional clauses into rewrites.  The zero case is easy.
postulate
  gKan-𝐳 : gKan 𝐳 ≡ ƛ A ⇒ (A !⁰ ≊ A !¹)
{-# REWRITE gKan-𝐳 #-}

-- Here is the "primary part" of kan, the "demotion" that extracts a
-- bitotal correspondence from an identification in the universe.
_↓ : {X₀ X₁ : Type} (X₂ : X₀ ＝ X₁) → X₀ ≊ X₁
_↓ {X₀} {X₁} X₂ = snd (kan {𝐬 𝐳} (★ ⸴ ★ ⸴ ★ ⸴ X₀ ⸴ X₁ , X₂))

-- Computationally, we regard "kan 𝐳" (informally) as a DESTRUCTOR of
-- a COINDUCTIVE UNIVERSE.  This means that whenever we introduce a
-- map into the universe (i.e. a type constructor), we must specify
-- how kan computes on it.  Giving such a computation law for a
-- particular type former amounts to specifying its identity types
-- along with its transport and lifting, which will generally be
-- instances of the same type former (so that this is morally a
-- corecursive definition, matching the coinductive nature of the
-- universe).

-- This also means that ap-kan, ap-ap-kan, and so on ought also to be
-- regarded as coinductive destructors (of ＝U, SqU, and so on).  In
-- particular, the computation laws for "kan" on type-formers should
-- lift to computation laws of ap-kan.  We will enforce this by
-- computing iterated ap/refl on type formers to a "corecursive
-- constructor" of higher cubes in the universe that essentially
-- specifies the output of higher "kan"s on itself, analogously to how
-- ap behaves on the introduction form of a √.

-- The behavior of (kan 2) on symmetry is simply given by the ordinary
-- rules of ap-ap on symmetry, together with the definition of
-- symmetry on √-types.  Although since (kan 2) reduces *from*
-- ap-ap-kan, we probably need a special rewrite rule for it, and more
-- generally for (kan (𝐬 (𝐬 n))).  As we will see, this specifies
-- precisely the primitive symmetrized squares that we need.

-- Finally, the fact that ap-kan is (informally) the destructor of a
-- coinductive ＝U means that it's sensible to add an additional
-- constructor of ＝U as long as we specify how ap-kan computes on it.
-- This will be the "promotion" rule taking a one-to-one
-- correspondence to an identification in the universe.

-- Intuitively, we can say that while Book HoTT specifies ∞-groupoid
-- structure *inductively*, and cubical type theory specifies it
-- *explicitly*, HOTT specifies it *coinductively*.

--------------------------------------------------
-- Comparing correspondences to identifications
--------------------------------------------------

-- The correspondence component of ((ap B e) ↓) is (Id B e), while the
-- other four components are transport and lifting, and similarly for
-- (refl B ↓) and (_＝_ {B}).  Morally, we regard these as
-- "definitions" of Id and ＝.  However, to actually "define" ＝ that
-- way (in the sense of rewriting (_＝_ {B}) to part of (refl B ↓))
-- would almost certainly be horribly circular, so we rewrite it in
-- the other direction.

postulate
  refl↓ : (A : Type) →
    -- _／_～_ (refl A ↓) ≡
    _／_～_ (snd (kan (★ ⸴ ★ ⸴ ★ ⸴ A ⸴ A , refl A))) ≡
    _＝_ {A}
{-# REWRITE refl↓ #-}

-- Because of the direction we compute in refl↓, for confluence we
-- need to give explicit analogues for ＝ of all the relevant rules
-- for refl.  On constructors of the universe, i.e. type formers, this
-- is all over the place.  What remains is eliminators mapping into
-- the universe.

postulate
  ＝-∙ : {A : Type} (f : A ⇒ Type) (a : A) (x₀ x₁ : f ∙ a) →
    (x₀ ＝ x₁) ≡ ((refl f ∙ (a , a , refl a) ↓) ／ x₀ ～ x₁)
  -- Note the directions of computation.
  --- refl (f ∙ a)             ⟼  refl f ∙ (a , a , refl a)                [by refl-∙]
  --- x₀ ~[ refl (f ∙ a) ] x₁  ⟼  (_＝_ {f ∙ a} x₀ x₁)                     [by refl↓]
  --- (_＝_ {f ∙ a} x₀ x₁)     ⟼  (x₀ ~[ refl f ∙ (a , a , refl a) ] x₁)   [by ＝-∙]
  -- Thus, ＝-∙ restores confluence between refl-∙ and refl↓.
  ＝-fst :  {B : Type → Type} (u : Σ Type B) (x₀ x₁ : fst u) →
    (x₀ ＝ x₁) ≡ (fst (refl u) ↓ ／ x₀ ～ x₁)
  ＝-snd : {A : Type} (u : A × Type) (x₀ x₁ : snd u) →
    (x₀ ＝ x₁) ≡ (snd (refl u) ↓ ／ x₀ ～ x₁)

{-# REWRITE ＝-∙ ＝-fst ＝-snd #-}

-- It's less clear that it's wrong to rewrite (Id B e) to become part
-- of ((ap B e) ↓), but when I tried this Agda spun forever.  Probably
-- it creates a loop somewhere.  So instead we will rewrite ap to Id,
-- in the same direction as refl to ＝.

postulate
  ap↓ : {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
    -- _／_～_ (ap B a₂ ↓) ≡
    _／_～_ (snd (kan (★ ⸴ ★ ⸴ ★ ⸴ B a₀ ⸴ B a₁ , ap B a₂))) ≡
    Id B a₂
{-# REWRITE ap↓ #-}

-- Again, we have to give analogues for Id of the computation rules
-- for ap on eliminators.

postulate
  Id-fst : {Δ : Type} {B : Δ → Type → Type} (u : (δ : Δ) → Σ Type (B δ)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (x₀ : fst (u δ₀)) (x₁ : fst (u δ₁)) →
    Id (λ δ → fst (u δ)) δ₂ x₀ x₁ ≡ (fst (ap u δ₂) ↓ ／ x₀ ～ x₁)
  Id-snd : {Δ : Type} (A : Δ → Type) (u : (δ : Δ) → Σ (A δ) (λ _ → Type)) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (x₀ : snd (u δ₀)) (x₁ : snd (u δ₁)) →
    Id (λ δ → snd (u δ)) δ₂ x₀ x₁ ≡ (snd (ap u δ₂) ↓ ／ x₀ ～ x₁)
  Id-∙ : {Δ : Type} {A : Δ → Type} (f : (δ : Δ) → A δ ⇒ Type)
    (a : (δ : Δ) → A δ) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (x₀ : f δ₀ ∙ a δ₀) (x₁ : f δ₁ ∙ a δ₁) →
    Id (λ δ → f δ ∙ a δ) δ₂ x₀ x₁ ≡ (ap f δ₂ ∙ (a δ₀ , a δ₁ , ap a δ₂) ↓ ／ x₀ ～ x₁)

{-# REWRITE Id-fst Id-snd Id-∙ #-}

-- We also need Id-analogues of the rules for ap on variables.  The
-- one for non-locally-bound variables is Id-const, analogous to
-- ap-const.  (Id-refl and ap-refl are also analogous, both morally
-- admissible but useful to have as primitive.)  The action on bound
-- variables is the analogue of ap-idmap:
postulate
  Id-idmap : {A₀ A₁ : Type} (A₂ : A₀ ＝ A₁) (a₀ : A₀) (a₁ : A₁) →
    Id (λ X → X) A₂ a₀ a₁ ≡ (A₂ ↓) ／ a₀ ～ a₁
{-# REWRITE Id-idmap #-}

------------------------------
-- Transport and lifting
------------------------------

-- The other components of ap-↓ are transport and lifting.

tr⇒ : {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → B a₀ ⇒ B a₁
tr⇒ {A} B {a₀} {a₁} a₂ = coe⇒ (ap B a₂ ↓)

tr⇐ : {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → B a₁ ⇒ B a₀
tr⇐ {A} B {a₀} {a₁} a₂ = coe⇐ (ap B a₂ ↓)

lift⇒ : {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
  （ b₀ ⦂ B a₀ ）⇒ Id B a₂ b₀ (tr⇒ B a₂ ∙ b₀)
lift⇒ {A} B {a₀} {a₁} a₂ = push⇒ (ap B a₂ ↓)

lift⇐ : {A : Type} (B : A → Type) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) →
  （ b₁ ⦂ B a₁ ）⇒ Id B a₂ (tr⇐ B a₂ ∙ b₁) b₁
lift⇐ {A} B {a₀} {a₁} a₂ = push⇐ (ap B a₂ ↓)

-- Similarly, the other components of refl-↓ are "nudges" and
-- "touches", which are trivial up to homotopy, but not definitionally
-- in general (lack of regularity).

nudge⇒ : {A : Type} → A ⇒ A
nudge⇒ {A} = coe⇒ (refl A ↓)

nudge⇐ : {A : Type} → A ⇒ A
nudge⇐ {A} = coe⇐ (refl A ↓)

touch⇒ : {A : Type} → （ a ⦂ A ）⇒ a ＝ nudge⇒ ∙ a
touch⇒ {A} = push⇒ (refl A ↓)

touch⇐ : {A : Type} → （ a ⦂ A ）⇒ nudge⇐ ∙ a ＝ a
touch⇐ {A} = push⇐ (refl A ↓)
