{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts #-}

module HOTT.Square.Heterogeneous where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe
open import HOTT.Square.Simple
open import HOTT.Exonat
--open import HOTT.Sqrt

------------------------------
-- Id-Id in the universe
------------------------------

-- This is the identity types of ≊, computed as if it were a Σ-type.
record Id≊ {A₀₀ A₀₁ : Type} (A₀₂ : A₀₀ ＝ A₀₁) {A₁₀ A₁₁ : Type} (A₁₂ : A₁₀ ＝ A₁₁)
  (A₂₀ : A₀₀ ≊ A₁₀) (A₂₁ : A₀₁ ≊ A₁₁) : Type where
  constructor Id≊[_,_,_,_,_]
  field
    ap-／ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁)
            {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
            (A₂₀ ／ a₀₀ ～ a₁₀) ＝ (A₂₁ ／ a₀₁ ～ a₁₁)
    ap-coe→ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁) →
      A₁₂ ↓ ／ coe⇒ A₂₀ ∙ a₀₀ ～ coe⇒ A₂₁ ∙ a₀₁
    ap-coe← : {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
      A₀₂ ↓ ／ coe⇐ A₂₀ ∙ a₁₀ ～ coe⇐ A₂₁ ∙ a₁₁
    ap-push→ : {a₀₀ : A₀₀} {a₀₁ : A₀₁} (a₀₂ : A₀₂ ↓ ／ a₀₀ ～ a₀₁) →
      ap-／ a₀₂ (ap-coe→ a₀₂) ↓ ／ push⇒ A₂₀ ∙ a₀₀ ～ push⇒ A₂₁ ∙ a₀₁
    ap-push← : {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a₁₂ : A₁₂ ↓ ／ a₁₀ ～ a₁₁) →
      ap-／ (ap-coe← a₁₂) a₁₂ ↓ ／ push⇐ A₂₀ ∙ a₁₀ ～ push⇐ A₂₁ ∙ a₁₁
open Id≊ public

postulate
  ＝-≊ : {A B : Type} (e₀ e₁ : A ≊ B) →
    (e₀ ＝ e₁) ≡ Id≊ (refl A) (refl B) e₀ e₁
  Id-≊ : {Δ : Type} (A B : Δ → Type) {δ₀ δ₁ : Δ} (δ₂ : δ₀ ＝ δ₁)
    (e₀ : A δ₀ ≊ B δ₀) (e₁ : A δ₁ ≊ B δ₁) →
    Id (λ δ → A δ ≊ B δ) δ₂ e₀ e₁ ≡ Id≊ (ap A δ₂) (ap B δ₂) e₀ e₁
{-# REWRITE ＝-≊ Id-≊ #-}

-- TODO: compute ap and refl on all the constructors and fields of ≊.
-- Also deal with the higher identity types of ≊ too.

------------------------------
-- Computing gKan on 𝐬
------------------------------

-- This is nice and fast when written with pattern-matching, but
-- prohibitively slow when written with projections.  Since our
-- Σ-types don't have η, that could conceivably be a problem, but
-- there's a chance that in practice we'll only be applying this to
-- actual tuples.
gKan𝐬 : (n : ℕᵉ) → ∂U (𝐬 (𝐬 n)) → Type
gKan𝐬 n ((A₀₀ , A₁₀ , A₂₀ , a₀₀ , a₁₀) , (A₀₁ , A₁₁ , A₂₁ , a₀₁ , a₁₁) , (A₀₂ , A₁₂ , A₂₂ , a₀₂ , a₁₂) , (a₂₀ , a₂₁)) =
  Id (gKan n) {A₀₀ , A₀₁ , A₀₂ , a₀₀ , a₀₁} {A₁₀ , A₁₁ , A₁₂ , a₁₀ , a₁₁}
     (A₂₀ , A₂₁ , sym (∂U n) ┌─  A₁₂  ─┐
                             A₂₀  □  A₂₁
                             └─  A₀₂  ─┘  A₂₂ , a₂₀ , a₂₁)
     (snd (kan {𝐬 n} a₀₂)) (snd (kan {𝐬 n} a₁₂))

postulate
  gKan-𝐬 : {n : ℕᵉ} (A : ∂U (𝐬 (𝐬 n))) →
    gKan (𝐬 n) A ≡ gKan𝐬 n A
{-# REWRITE gKan-𝐬 #-}

----------------------------------------
-- Heterogeneous squares
----------------------------------------

record ∂ʰ {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  (a₀₀ : A₀₀) (a₀₁ : A₀₁) (a₁₀ : A₁₀) (a₁₁ : A₁₁) : Typeᵉ where
  constructor ┏━_━┓_□_┗━_━┛
  infix 70 _₁₂ _₂₀ _₂₁ _₀₂
  field
    _₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁
    _₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀
    _₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁
    _₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁
open ∂ʰ public

sym-∂ʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} {A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁} {A₂₂ : Sq Type A}
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} →
  ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁ → ∂ʰ (sym-∂ A) (sym Type A A₂₂) a₀₀ a₁₀ a₀₁ a₁₁
sym-∂ʰ a = ┏━   a ₂₁   ━┓
           a ₀₂  □   a ₁₂
           ┗━   a ₂₀   ━┛

Sqʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) → Type
Sqʰ {A₀₀} {A₀₁} {A₁₀} {A₁₁} A A₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  ap-／ {A₀₀} {A₀₁} {A ₀₂} {A₁₀} {A₁₁} {A ₁₂} {A ₂₀ ↓} {A ₂₁ ↓} (snd (fst (kan {𝐬 (𝐬 𝐳)} A₂₂)))
    {a₀₀} {a₀₁} (a ₀₂) {a₁₀} {a₁₁} (a ₁₂) ↓ ／ a ₂₀ ～ (a ₂₁)

-- The other component of kan is a primitive symmetrized square.  The
-- two are interchanged by symmetry acting on U, and are isomorphic to
-- each other by a postulated heterogeneous symmetry.

Symʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) → Type
Symʰ {A₀₀} {A₀₁} {A₁₀} {A₁₁} A A₂₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a =
  ap-／ {A₀₀} {A₁₀} {A ₂₀} {A₀₁} {A₁₁} {A ₂₁} {A ₀₂ ↓} {A ₁₂ ↓} (snd (kan {𝐬 (𝐬 𝐳)} A₂₂))
    {a₀₀} {a₁₀} (a ₂₀) {a₀₁} {a₁₁} (a ₂₁) ↓ ／ a ₀₂ ～ (a ₁₂)

-- TODO: Heterogeneous squares in refl-refl are ordinary squares

-- TODO: Heterogeneous squares in ap-ap are dependent squares

------------------------------
-- Heterogeneous symmetry
------------------------------

postulate
  symʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) →
    Sqʰ A A₂₂ a → Symʰ (sym-∂ A) (sym Type A A₂₂) (sym-∂ʰ a)
  unsymʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁) →
    Symʰ A A₂₂ a → Sqʰ (sym-∂ A) (sym Type A A₂₂) (sym-∂ʰ a)
postulate
  unsym-symʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sqʰ A A₂₂ a) →
    -- This might need some green slime removed.
    unsymʰ (sym-∂ A) (sym Type A A₂₂) (sym-∂ʰ a) (symʰ A A₂₂ a a₂₂) ≡ a₂₂
  sym-unsymʰ : {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
    {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} (a : ∂ʰ A A₂₂ a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Symʰ A A₂₂ a) →
    -- This might need some green slime removed.
    symʰ (sym-∂ A) (sym Type A A₂₂) (sym-∂ʰ a) (unsymʰ A A₂₂ a a₂₂) ≡ a₂₂
{-# REWRITE unsym-symʰ sym-unsymʰ #-}

-- TODO: symʰ computes on ap to symᵈ, and on refl to sym.

--------------------------------------------------
-- Heterogeneous composition and filling
--------------------------------------------------

IDʰ : Type
IDʰ = （ A₀ ⦂ Type ）× （ A₁ ⦂ Type ）× （ A₂ ⦂ A₀ ＝ A₁ ）× A₀ × A₁

Idʰ : IDʰ → Type
Idʰ A = ₃rd A ↓ ／ ₄th A ～ ₅th' A

module _  {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} where

  compʰ→ : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) →
    A ₂₁ ↓ ／ a₀₁ ～ a₁₁
  compʰ→ a₀₂ a₁₂ a₂₀ = tr⇒ Idʰ {A₀₀ , A₁₀ , A ₂₀ , a₀₀ , a₁₀} {A₀₁ , A₁₁ , A ₂₁ , a₀₁ , a₁₁} (A ₀₂ , A ₁₂ , A₂₂ , a₀₂ , a₁₂) ∙ a₂₀

  -- Needs a rule for Id in _／_～_, which is an analogue of ap on it.
  fillʰ→ : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) →
    Sqʰ A A₂₂ ┏━   a₁₂   ━┓
              a₂₀  □   compʰ→ a₀₂ a₁₂ a₂₀
              ┗━   a₀₂   ━┛
  fillʰ→ a₀₂ a₁₂ a₂₀ = {!lift⇒ Idʰ {A₀₀ , A₁₀ , A ₂₀ , a₀₀ , a₁₀} {A₀₁ , A₁₁ , A ₂₁ , a₀₁ , a₁₁} (A ₀₂ , A ₁₂ , A₂₂ , a₀₂ , a₁₂) ∙ a₂₀!}

  compʰ← : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    A ₂₀ ↓ ／ a₀₀ ～ a₁₀
  compʰ← a₀₂ a₁₂ a₂₁ = tr⇐ Idʰ {A₀₀ , A₁₀ , A ₂₀ , a₀₀ , a₁₀} {A₀₁ , A₁₁ , A ₂₁ , a₀₁ , a₁₁} (A ₀₂ , A ₁₂ , A₂₂ , a₀₂ , a₁₂) ∙ a₂₁

  fillʰ← : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    Sqʰ A A₂₂ ┏━                 a₁₂   ━┓
              compʰ← a₀₂ a₁₂ a₂₁  □    a₂₁
              ┗━                 a₀₂   ━┛
  fillʰ← a₀₂ a₁₂ a₂₁ = {!lift⇐ Idʰ {A₀₀ , A₁₀ , A ₂₀ , a₀₀ , a₁₀} {A₀₁ , A₁₁ , A ₂₁ , a₀₁ , a₁₁} (A ₀₂ , A ₁₂ , A₂₂ , a₀₂ , a₁₂) ∙ a₂₁!}

module _  {A₀₀ A₀₁ A₁₀ A₁₁ : Type} (A : ∂ Type A₀₀ A₀₁ A₁₀ A₁₁) (A₂₂ : Sq Type A)
  {a₀₀ : A₀₀} {a₀₁ : A₀₁} {a₁₀ : A₁₀} {a₁₁ : A₁₁} where

  compʰ↑ : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    A ₁₂ ↓ ／ a₁₀ ～ a₁₁
  compʰ↑ a₀₂ a₂₀ a₂₁ = compʰ→ (sym-∂ A) (sym Type A A₂₂) a₂₀ a₂₁ a₀₂

  fillʰ↑ : (a₀₂ : A ₀₂ ↓ ／ a₀₀ ～ a₀₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    Sqʰ A A₂₂ ┏━  compʰ↑ a₀₂ a₂₀ a₂₁   ━┓
              a₂₀         □           a₂₁
              ┗━         a₀₂          ━┛
  fillʰ↑ a₀₂ a₂₀ a₂₁ = unsymʰ (sym-∂ A) (sym Type A A₂₂) ┏━   a₂₁   ━┓
                                                         a₀₂  □   compʰ↑ a₀₂ a₂₀ a₂₁
                                                         ┗━   a₂₀   ━┛
  -- Need a version of (fillʰ→ (sym-∂ A) (sym Type A A₂₂) a₂₀ a₂₁ a₀₂)
  -- that lies in Symʰ.  Maybe this means compʰ↑ should be defined
  -- using Symʰ rather than Idʰ?
                       {!!}

  compʰ↓ : (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
     A ₀₂ ↓ ／ a₀₀ ～ a₀₁
  compʰ↓ a₁₂ a₂₀ a₂₁ = compʰ← (sym-∂ A) (sym Type A A₂₂) a₂₀ a₂₁ a₁₂

  fillʰ↓ : (a₁₂ : A ₁₂ ↓ ／ a₁₀ ～ a₁₁) (a₂₀ : A ₂₀ ↓ ／ a₀₀ ～ a₁₀) (a₂₁ : A ₂₁ ↓ ／ a₀₁ ～ a₁₁) →
    Sqʰ A A₂₂ ┏━         a₁₂           ━┓
              a₂₀         □           a₂₁
              ┗━  compʰ↓ a₁₂ a₂₀ a₂₁   ━┛
  fillʰ↓ a₁₂ a₂₀ a₂₁ = unsymʰ (sym-∂ A) (sym Type A A₂₂) ┏━                 a₂₁   ━┓
                                                         compʰ↓ a₁₂ a₂₀ a₂₁  □   a₁₂
                                                         ┗━                a₂₀   ━┛
                       {!!}
