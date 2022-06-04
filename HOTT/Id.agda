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
  -- Dependent/heterogeneous identity telescopes
  ID′ : {Δ : Tel} (Θ : el Δ → Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (t₀ : el (Θ δ₀)) (t₁ : el (Θ δ₁)) → Tel

-- Identity telescopes are built up from (dependent) identity types
postulate
  IDε : (δ₀ δ₁ : el ε) → ID ε δ₀ δ₁ ≡ ε
  ID▸ : (Δ : Tel) (A : el Δ → Type) (δ₀ δ₁ : el (Δ ▸ A)) →
    ID (Δ ▸ A) δ₀ δ₁ ≡ ID Δ (pop δ₀) (pop δ₁) ▸ λ δ₂ → Id′ A δ₂ (top δ₀) (top δ₁)
  ID► : {Δ : Tel} (Θ : el Δ → Tel) (h₀ h₁ : el (Δ ► Θ)) →
    ID (Δ ► Θ) h₀ h₁ ≡ ID Δ (POP Θ h₀) (POP Θ h₁) ► λ w₂ → ID′ Θ w₂ (TOP Θ h₀) (TOP Θ h₁)

{-# REWRITE IDε ID▸ ID► #-}

-- Dependent identity telescopes are also built up from (dependent) identity types
postulate
  -- Id′ε would follow from IDε and ID′-CONST
  ID′ε : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (t₀ t₁ : el ε) → ID′ {Δ} (λ _ → ε) δ₂ t₀ t₁ ≡ ε
  ID′▸ : {Δ : Tel} (Θ : el Δ → Tel) (A : (w : el Δ) → el (Θ w) → Type)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (t₀ : el (Θ δ₀ ▸ A δ₀)) (t₁ : el (Θ δ₁ ▸ A δ₁)) →
    ID′ (λ w → Θ w ▸ A w) δ₂ t₀ t₁ ≡
    ID′ Θ δ₂ (pop t₀) (pop t₁) ▸
    (λ t₂ → Id′ {Δ ► Θ} (UNCURRY Θ A) {PAIR Θ δ₀ (pop t₀)} {PAIR Θ δ₁ (pop t₁)}
            (PAIR (λ w → ID′ Θ w (pop t₀) (pop t₁)) δ₂ t₂)
            (top t₀) (top t₁))
  ID′► : {Δ : Tel} (Θ : el Δ → Tel) (Γ : (w : el Δ) → el (Θ w) → Tel)
    {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (t₀ : el (Θ δ₀ ► Γ δ₀)) (t₁ : el (Θ δ₁ ► Γ δ₁)) →
    ID′ (λ w → Θ w ► Γ w) δ₂ t₀ t₁ ≡
    ID′ Θ δ₂ (POP (Γ δ₀) t₀) (POP (Γ δ₁) t₁) ►
    (λ t₂ → ID′ {Δ ► Θ} (UNCURRY Θ Γ) {PAIR Θ δ₀ (POP (Γ δ₀) t₀)} {PAIR Θ δ₁ (POP (Γ δ₁) t₁)}
            (PAIR (λ w → ID′ Θ w (POP (Γ δ₀) t₀) (POP (Γ δ₁) t₁)) δ₂ t₂)
            (TOP (Γ δ₀) t₀) (TOP (Γ δ₁) t₁))

{-# REWRITE ID′ε ID′▸ ID′► #-}

----------------------------------------
-- Telescope ap and functoriality, I
----------------------------------------

postulate
  -- Since Id will be definitionally a special case of Id′, we don't
  -- need separate and non-dependent versions of ap.
  ap : {Δ : Tel} {A : el Δ → Type} (f : (δ : el Δ) → A δ) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → Id′ A δ₂ (f δ₀) (f δ₁)
  -- However, for telescopes we do, since ID is not a special case of ID′.
  AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) → el (ID Δ (f t₀) (f t₁))
  AP′ : {Θ : Tel} (Δ : el Θ → Tel) (f : (x : el Θ) → el (Δ x)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    el (ID′ Δ t₂ (f t₀) (f t₁))

-- We assert that ID′ in a constant family is equal to ID, and
-- similarly for AP′ and AP.
postulate
  ID′-CONST : {Θ : Tel} (Δ : Tel) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (δ₀ δ₁ : el Δ) →
    ID′ {Θ} (λ _ → Δ) t₂ δ₀ δ₁ ≡ ID Δ δ₀ δ₁
  AP′-CONST : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP′ (λ _ → Δ) f t₂ ≡ COE← (ID′-CONST Δ t₂ (f t₀) (f t₁)) (AP f t₂)

-- It's tempting to declare these as rewrites, but that seems to lead
-- to ill-typed terms.  Thus, we will instead (below) specify how to
-- reduce these equalities on concrete telescopes.
--- {-# REWRITE ID′-CONST AP′-CONST #-}

-- Below we will give rewrite rules computing ap on type-formers, and
-- AP and AP′ on telescope-formers.  The simplest of these is the
-- action of AP on the identity, which is part of its functoriality.
postulate
  AP-idmap : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) → AP {Δ} {Δ} (λ w → w) δ₂ ≡ δ₂ 
  AP′-idmap : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) →
    AP′ {Δ} (λ _ → Δ) (λ w → w) δ₂ ≡ COE← (ID′-CONST Δ δ₂ δ₀ δ₁) δ₂

{-# REWRITE AP-idmap AP′-idmap #-}

-- Functoriality for composition is only ADMISSIBLE, so these are not
-- rewrites.  (Functoriality on the identity is also technically
-- admissible, but unproblematic to make a rewrite in general.)
postulate
  Id′-AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (A : el Δ → Type) (a₀ : A (f t₀)) (a₁ : A (f t₁)) →
    Id′ A (AP f t₂) a₀ a₁ ≡ Id′ (λ w → A (f w)) t₂ a₀ a₁
  Id′-AP′ : {Θ : Tel} (Δ : el Θ → Tel) (f : (x : el Θ) → el (Δ x)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (A : (x : el Θ) → el (Δ x) → Type) (a₀ : A t₀ (f t₀)) (a₁ : A t₁ (f t₁)) →
    Id′ (UNCURRY Δ A) {PAIR Δ t₀ (f t₀)} {PAIR Δ t₁ (f t₁)} (PAIR (λ w₂ → ID′ Δ w₂ (f t₀) (f t₁)) t₂ (AP′ Δ f t₂)) a₀ a₁ ≡
    Id′ (λ w → A w (f w)) t₂ a₀ a₁
  ap-AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {A : el Δ → Type} (g : (x : el Δ) → A x) →
    ap g (AP f t₂) ≡ coe← (Id′-AP f t₂ A (g (f t₀)) (g (f t₁))) (ap (λ w → g (f w)) t₂)

-- We "prove" these admissible rules by giving rewrites saying how
-- they behave on concrete terms.  The simplest such rule is how they
-- act on the identity.
postulate
  Id′-AP-idmap : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (A : el Δ → Type) (a₀ : A δ₀) (a₁ : A δ₁) →
    Id′-AP {Δ} {Δ} (λ w → w) δ₂ A a₀ a₁ ≡ reflᵉ

{-# REWRITE Id′-AP-idmap #-}

-- We have similar rules for identity telescopes, which should be
-- "composed" of the corresponding rules for ordinary identity types.
postulate
  ID′-AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (Γ : el Δ → Tel) (γ₀ : el (Γ (f t₀))) (γ₁ : el (Γ (f t₁))) →
    ID′ Γ (AP f t₂) γ₀ γ₁ ≡ ID′ (λ w → Γ (f w)) t₂ γ₀ γ₁
  ID′-AP′ : {Θ : Tel} (Δ : el Θ → Tel) (f : (x : el Θ) → el (Δ x)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (Γ : (x : el Θ) → el (Δ x) → Tel) (γ₀ : el (Γ t₀ (f t₀))) (γ₁ : el (Γ t₁ (f t₁))) →
    ID′ (UNCURRY Δ Γ) {PAIR Δ t₀ (f t₀)} {PAIR Δ t₁ (f t₁)} (PAIR (λ w₂ → ID′ Δ w₂ (f t₀) (f t₁)) t₂ (AP′ Δ f t₂)) γ₀ γ₁ ≡
    ID′ (λ w → Γ w (f w)) t₂ γ₀ γ₁
  AP-AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {Γ : Tel} (g : el Δ → el Γ) →
    AP g (AP f t₂) ≡ AP (λ w → g (f w)) t₂
  AP′-AP : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {Γ : el Δ → Tel} (g : (x : el Δ) → el (Γ x)) →
    AP′ Γ g (AP f t₂) ≡ COE← (ID′-AP f t₂ Γ (g (f t₀)) (g (f t₁))) (AP′ (λ w → Γ (f w)) (λ w → g (f w)) t₂) 

-- We ensure this "composition" property by giving rewrite rules.  The
-- simplest are the ones for ε and [].
postulate
  ID′-AP-ε : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (γ₀ γ₁ : el ε) →
    ID′-AP f t₂ (λ _ → ε) γ₀ γ₁ ≡ reflᵉ
  ID′-AP′-ε : {Θ : Tel} (Δ : el Θ → Tel) (f : (x : el Θ) → el (Δ x)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (γ₀ γ₁ : el ε) →
    ID′-AP′ Δ f t₂ (λ _ _ → ε) γ₀ γ₁ ≡ reflᵉ

{-# REWRITE ID′-AP-ε ID′-AP′-ε #-}

postulate
  AP-AP-[] : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP-AP f t₂ (λ _ → []) ≡ reflᵉ
  AP′-AP-[] : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP′-AP f t₂ (λ _ → []) ≡ reflᵉ

{-# REWRITE AP-AP-[] AP′-AP-[] #-}

-- ID′-AP-▸ and ID′-AP′-▸ require some computation rules for AP, so we
-- postpone them to later.

-- The next simplest are the ones for the identity.
postulate
  ID′-AP-idmap : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (Θ : el Δ → Tel) (t₀ : el (Θ δ₀)) (t₁ : el (Θ δ₁)) →
    ID′-AP {Δ} {Δ} (λ w → w) δ₂ Θ t₀ t₁ ≡ reflᵉ
  -- ID′-AP′-idmap requires a computation rule for AP, so it comes later.
  AP-AP-idmap : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP-AP f t₂ (λ x → x) ≡ reflᵉ

{-# REWRITE ID′-AP-idmap AP-AP-idmap #-}

postulate
  AP′-AP-idmap : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) →
    AP′-AP f t₂ (λ x → x) ≡ 
    (rev (COE←COE← (ID′-AP f t₂ (λ _ → Δ) (f t₀) (f t₁)) (ID′-CONST Δ t₂ (f t₀) (f t₁)) (ID′-CONST Δ (AP f t₂) (f t₀) (f t₁)))
     • cong (COE← (ID′-AP f t₂ (λ _ → Δ) (f t₀) (f t₁))) (rev (AP′-CONST f t₂)))

{-# REWRITE AP′-AP-idmap #-}

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

------------------------------
-- Functoriality, II
------------------------------

-- We can now return to some functoriality rules that couldn't be
-- stated until we had the above rules for computing AP and AP′.

{-
postulate
  ID′-AP-▸ : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (Γ : el Δ → Tel) (A : (x : el Δ) → el (Γ x) → Type) (γ₀ : el (Γ (f t₀) ▸ A (f t₀))) (γ₁ : el (Γ (f t₁) ▸ A (f t₁))) →
    ID′-AP f t₂ (λ x → Γ x ▸ A x) γ₀ γ₁ ≡
    (ID′-AP f t₂ Γ (pop γ₀) (pop γ₁) ▸≡
     ≡λ′← λ x₁ → {!!} •
                  Id′-AP (λ w → PAIR Γ (f (POP (λ x → Γ (f x)) w)) (TOP (λ x → Γ (f x)) w))
                         {PAIR (λ z → Γ (f z)) t₀ (pop γ₀)} {PAIR (λ z → Γ (f z)) t₁ (pop γ₁)}
                         (PAIR (λ w → ID′ (λ z → Γ (f z)) w (pop γ₀) (pop γ₁)) t₂ x₁) (UNCURRY Γ A) (top γ₀) (top γ₁))
-- TODO: ID′-AP′-▸
-}

postulate
  Id′-AP′-idmap : {Δ : Tel} {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁))
    (A : el Δ → Type) (a₀ : A δ₀) (a₁ : A δ₁) →
    Id′-AP′ {Δ} (λ _ → Δ) (λ w → w) δ₂ (λ _ → A) a₀ a₁ ≡ Id′-AP (λ w → PR Δ Δ w w) δ₂ (UNCURRY (λ _ → Δ) (λ _ → A)) a₀ a₁  

{-# REWRITE Id′-AP′-idmap #-}

-- TODO: computing AP-AP and AP′-AP at least on ∷, and maybe on top, pop, TOP, POP, PAIR?

-- Note that ap-top, AP′-pop, AP′-CONST, and AP-idmap combine to
-- determine the correct effect of ap on variables occurring in the
-- telescope.  (Variables not occurring in the telescope are
-- constants, handled by ap-const.)

postulate
  ID′-CONST-ε : {Θ : Tel} {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (δ₀ δ₁ : el ε) →
    ID′-CONST {Θ} ε t₂ δ₀ δ₁ ≡ reflᵉ
  ID′-CONST-▸ : {Θ : Tel} (Δ : Tel) (A : el Δ → Type) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
    (δ₀ δ₁ : el Δ) (a₀ : A δ₀) (a₁ : A δ₁) →
    ID′-CONST {Θ} (Δ ▸ A) t₂ (δ₀ ∷ a₀) (δ₁ ∷ a₁) ≡
    (ID′-CONST {Θ} Δ t₂ δ₀ δ₁ ▸≡
      ≡λ′→ λ x₀ → rev (Id′-AP (SND Θ Δ) (PAIR (λ w → ID′ (λ _ → Δ) w δ₀ δ₁) t₂ x₀) A a₀ a₁))

-- Produces an internal error with --two-level
{-# REWRITE ID′-CONST-ε ID′-CONST-▸ #-}


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
  Id-const : {Δ : Tel} (A : Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a₀ a₁ : A) →
    Id′ {Δ} (λ _ → A) δ₂ a₀ a₁ ≡ Id A a₀ a₁
  -- (Recall we already asserted ID′-CONST above.)

{-# REWRITE Id-const #-}

-- Similarly, reflexivity is nullary ap, with the same caveat.
postulate
  refl : {A : Type} (a : A) → Id A a a
  ap-const : {Δ : Tel} (A : Type) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (a : A) →
    ap {Δ} (λ _ → a) δ₂ ≡ refl a
  REFL : {Δ : Tel} (δ : el Δ) → el (ID Δ δ δ)
  AP-const : {Δ : Tel} (Θ : Tel) {δ₀ δ₁ : el Δ} (δ₂ : el (ID Δ δ₀ δ₁)) (t : el Θ) →
    AP {Δ} (λ _ → t) δ₂ ≡ REFL t

{-# REWRITE ap-const AP-const #-}

-- Functoriality on reflexivity is then a special case of general
-- functoriality on ap.
Id-REFL : {Δ : Tel} (A : el Δ → Type) (δ : el Δ) (a₀ a₁ : A δ) → Id′ A (REFL δ) a₀ a₁ ≡ Id (A δ) a₀ a₁
Id-REFL {Δ} A δ a₀ a₁ = Id′-AP {ε} (λ _ → δ) [] A a₀ a₁

ID-REFL : {Δ : Tel} (Θ : el Δ → Tel) (δ : el Δ) (t₀ t₁ : el (Θ δ)) → ID′ Θ (REFL δ) t₀ t₁ ≡ ID (Θ δ) t₀ t₁
ID-REFL {Δ} Θ δ t₀ t₁ = ID′-AP {ε} (λ _ → δ) [] Θ t₀ t₁ • ID′-CONST (Θ δ) [] t₀ t₁ 

-- We allow ourselves to rewrite along these, even though they are
-- technically admissible rules like Id′-AP, because they're more
-- obviously "directed" and something we can match on.

{-# REWRITE Id-REFL ID-REFL #-}

-- This makes ID′-CONST over ε into an identity.
postulate
  ID′-CONST-ε₁ : {Δ : Tel} (δ₀ δ₁ : el Δ) → ID′-CONST {ε} Δ [] δ₀ δ₁ ≡ reflᵉ

{-# REWRITE ID′-CONST-ε₁ #-}

-- The usefulness of this is limited in practice, because if δ has
-- internal structure, REFL will compute on it, and can't be
-- "un-rewritten" back to a REFL in order for Id-REFL to fire.  So we
-- still sometimes have to coerce along Id-REFL and ID-REFL.  However,
-- we minimize the effect of those by also postulating that they are
-- reflexivity, so that in situations where it's possible, the
-- coercion gets reduced away.
postulate
  Id-REFL-reflᵉ : {Δ : Tel} (A : el Δ → Type) (δ : el Δ) (a₀ a₁ : A δ) →
    Id′-AP {ε} (λ _ → δ) [] A a₀ a₁ ≡ reflᵉ
  ID-REFL-reflᵉ : {Δ : Tel} (Θ : el Δ → Tel) (δ : el Δ) (t₀ t₁ : el (Θ δ)) →
    ID′-AP {ε} (λ _ → δ) [] Θ t₀ t₁ ≡ reflᵉ

{-# REWRITE Id-REFL-reflᵉ ID-REFL-reflᵉ #-}

-- Now we can do the same for ap on REFL.

ap-REFL : {Δ : Tel} (A : el Δ → Type) (f : (δ : el Δ) → A δ) (δ : el Δ) →
  ap f (REFL δ) ≡ refl (f δ)
ap-REFL {Δ} A f δ = ap-AP {ε} (λ _ → δ) [] f  

AP-REFL : {Δ Θ : Tel} (f : el Δ → el Θ) (δ : el Δ) →
  AP f (REFL δ) ≡ REFL (f δ)
AP-REFL f δ = AP-AP {ε} (λ _ → δ) [] f

AP′-REFL : {Δ : Tel} (Θ : el Δ → Tel) (f : (δ : el Δ) → el (Θ δ)) (δ : el Δ) →
  AP′ Θ f (REFL δ) ≡ REFL (f δ)
AP′-REFL {Δ} Θ f δ = AP′-AP {ε} (λ _ → δ) [] f • AP′-CONST {ε} (λ _ → f δ) []

{-# REWRITE ap-REFL AP-REFL AP′-REFL #-}

-- We can now assert that the functoriality rules for constant
-- families and functions reduce to reflexivity, which is well-typed
-- since both sides reduce to a homogeneous Id or a refl.
postulate
  Id′-AP-const : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (A : Type) (a₀ a₁ : A) →
    Id′-AP f t₂ (λ _ → A) a₀ a₁ ≡ reflᵉ
  Id′-AP′-const : {Θ : Tel} (Δ : el Θ → Tel) (f : (x : el Θ) → el (Δ x))
    {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (A : Type) (a₀ a₁ : A) →
    Id′-AP′ Δ f t₂ (λ _ _ → A) a₀ a₁ ≡ reflᵉ
{-
  ID′-AP-const : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) (Γ : Tel) (γ₀ γ₁ : el Γ) →
    ID′-AP f t₂ (λ _ → Γ) γ₀ γ₁ ≡ {! reflᵉ !}
  ID′-AP′-const : {Θ : Tel} (Δ : el Θ → Tel) (f : (x : el Θ) → el (Δ x)) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁))
                 (Γ : Tel) (γ₀ γ₁ : el Γ) →
    ID′-AP′ Δ f t₂ (λ _ _ → Γ) γ₀ γ₁ ≡ {! reflᵉ!}
-}

{-# REWRITE Id′-AP-const Id′-AP′-const #-}

-- ID′-AP-const ID′-AP′-const #-}

postulate
  ap-AP-const : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {A : Type} (g : A) →
    ap-AP f t₂ (λ _ → g) ≡ reflᵉ
  AP-AP-const : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {Γ : Tel} (g : el Γ) →
    AP-AP f t₂ (λ _ → g) ≡ reflᵉ
{-
  AP′-AP-const : {Θ Δ : Tel} (f : el Θ → el Δ) {t₀ t₁ : el Θ} (t₂ : el (ID Θ t₀ t₁)) {Γ : Tel} (g : el Γ) →
    AP′-AP f t₂ (λ _ → g) ≡ {! reflᵉ !}
-}

{-# REWRITE ap-AP-const AP-AP-const #-}

-- AP′-AP-const #-}

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

{-# REWRITE REFL-TOP refl-top #-}

-- Similarly, in later files where we introduce particular type
-- formers, we must give separately their rules for homogeneous and
-- heterogeneous Id, and also separately the rules for ap and for refl
-- on their terms.
