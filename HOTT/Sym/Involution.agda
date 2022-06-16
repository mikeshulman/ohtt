{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --cumulativity --without-K #-}

module HOTT.Sym.Involution where

open import HOTT.Rewrite
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Square.Base
open import HOTT.Square.Top
open import HOTT.Square.Equality
open import HOTT.Sym.Base

------------------------------
-- Symmetry is an involution
------------------------------

-- We postulate that symmetry on types is an involution, and mutually
-- prove from this that it is an involution on telescopes.

SYM-SYM : (Δ : Tel) (δ : el (SQ Δ)) → SYM Δ (SYM Δ δ) ≡ δ

-- We would like to declare symmetry on types as a rewrite.  (Symmetry
-- on telescopes doesn't make as much sense as a rewrite, since it
-- involves coercions along the equalities SYMₘₙ that aren't rewrites,
-- but having symmetry on types be a rewrite should imply that
-- symmetry on concrete telescopes also rewrites.)  Unfortunately, the
-- naive postulate that would look something like
---
--- sym-sym : ... → sym A (SYM Δ δ) ... (sym A δ ... a₂₂) ≡ a₂₂
---
-- isn't suitable as a rewrite, because it has the volatile SYM on the
-- left.  When Δ is concrete, this SYM will reduce, and Agda won't be
-- able to un-reduce it to notice that the two sym's match.  This is
-- the main reason for postulating instead the enhanced symmetry sym′,
-- that incorporates coercion across equalities.  It allows us to
-- formulate sym-sym′, below, whose LHS is not volatile and can
-- hopefully be pattern-matched so that the rewrite will fire.

postulate
  sym-sym′ : {Δ : Tel} (A : el Δ → Type) (δ : el (SQ Δ))
    {a₀₀ : A (δ ₀₀)} {a₀₁ : A (δ ₀₁)} (a₀₂ : Id′ A (δ ₀₂) a₀₀ a₀₁)
    {a₁₀ : A (δ ₁₀)} {a₁₁ : A (δ ₁₁)} (a₁₂ : Id′ A (δ ₁₂) a₁₀ a₁₁)
    (a₂₀ : Id′ A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id′ A (δ ₂₁) a₀₁ a₁₁)
    {δ' : el (SQ Δ)} (ϕ : δ' ≡ SYM Δ δ)
    {a₀₀' : A (δ' ₀₀)} {a₀₁' : A (δ' ₀₁)} (a₀₂' : Id′ A (δ' ₀₂) a₀₀' a₀₁')
    {a₁₀' : A (δ' ₁₀)} {a₁₁' : A (δ' ₁₁)} (a₁₂' : Id′ A (δ' ₁₂) a₁₀' a₁₁')
    (a₂₀' : Id′ A (δ' ₂₀) a₀₀' a₁₀') (a₂₁' : Id′ A (δ' ₂₁) a₀₁' a₁₁')
    (e₀₀ : a₀₀' ≡ʰ a₀₀) (e₀₁ : a₀₁' ≡ʰ a₁₀) (e₀₂ : a₀₂' ≡ʰ a₂₀)
    (e₁₀ : a₁₀' ≡ʰ a₀₁) (e₁₁ : a₁₁' ≡ʰ a₁₁) (e₁₂ : a₁₂' ≡ʰ a₂₁)
    (e₂₀ : a₂₀' ≡ʰ a₀₂) (e₂₁ : a₂₁' ≡ʰ a₁₂)
    {δ'' : el (SQ Δ)} (ϕ' : δ'' ≡ SYM Δ δ')
    {a₀₀'' : A (δ'' ₀₀)} {a₀₁'' : A (δ'' ₀₁)} (a₀₂'' : Id′ A (δ'' ₀₂) a₀₀'' a₀₁'')
    {a₁₀'' : A (δ'' ₁₀)} {a₁₁'' : A (δ'' ₁₁)} (a₁₂'' : Id′ A (δ'' ₁₂) a₁₀'' a₁₁'')
    (a₂₀'' : Id′ A (δ'' ₂₀) a₀₀'' a₁₀'') (a₂₁'' : Id′ A (δ'' ₂₁) a₀₁'' a₁₁'')
    (e₀₀' : a₀₀'' ≡ʰ a₀₀') (e₀₁' : a₀₁'' ≡ʰ a₁₀') (e₀₂' : a₀₂'' ≡ʰ a₂₀')
    (e₁₀' : a₁₀'' ≡ʰ a₀₁') (e₁₁' : a₁₁'' ≡ʰ a₁₁') (e₁₂' : a₁₂'' ≡ʰ a₂₁')
    (e₂₀' : a₂₀'' ≡ʰ a₀₂') (e₂₁' : a₂₁'' ≡ʰ a₁₂')
    (a₂₂ : Sq A δ a₀₂ a₁₂ a₂₀ a₂₁) →
    sym′ A δ' a₀₂' a₁₂' a₂₀' a₂₁' ϕ' a₀₂'' a₁₂'' a₂₀'' a₂₁'' e₀₀' e₀₁' e₀₂' e₁₀' e₁₁' e₁₂' e₂₀' e₂₁'
      (sym′ A δ a₀₂ a₁₂ a₂₀ a₂₁ ϕ a₀₂' a₁₂' a₂₀' a₂₁' e₀₀ e₀₁ e₀₂ e₁₀ e₁₁ e₁₂ e₂₀ e₂₁ a₂₂) ≡
    coe← (Id′≡ (λ y → Id′ A (pop (pop y)) (top (pop y)) (top y))
           (sq₁₂≡ A (ϕ' • (cong (SYM Δ) ϕ) • SYM-SYM Δ δ)
             (e₀₀' •ʰ e₀₀) (e₀₁' •ʰ e₁₀) (e₀₂' •ʰ e₂₀) (e₁₀' •ʰ e₀₁) (e₁₁' •ʰ e₁₁) (e₁₂' •ʰ e₂₁))
           (e₂₀' •ʰ e₀₂) (e₂₁' •ʰ e₁₂))
         a₂₂

-- The extra freedom in sym-sym′ is also convenient when proving SYM-SYM.

-- With SYM₀₀ etc as refls, sym normalizes to
{-
  sym′ A δ a₀₂ a₁₂ a₂₀ a₂₁ reflᵉ
  (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
  (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
  (coe← (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) a₀₂)
  (coe← (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ) a₁₂)
  reflʰ
  reflʰ
  (coe←≡ʰ (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) a₂₀)
  reflʰ
  reflʰ
  (coe←≡ʰ (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) a₂₁)
  (coe←≡ʰ (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) a₀₂)
  (coe←≡ʰ (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ) a₁₂) a₂₂
-}
-- So the top of (SYM (Δ ▸ A) δ) becomes
{-
(sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ) (top₂₂ δ))
=
  sym′ A δ (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ) reflᵉ
  (coe← (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) (top₂₀ δ))
  (coe← (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) (top₂₁ δ))
  (coe← (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) (top₀₂ δ))
  (coe← (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ) (top₁₂ δ))
  reflʰ
  reflʰ
  (coe←≡ʰ (Id′≡ A (SYM₀₂ δ) reflʰ reflʰ) (top₂₀ δ))
  reflʰ
  reflʰ
  (coe←≡ʰ (Id′≡ A (SYM₁₂ δ) reflʰ reflʰ) (top₂₁ δ))
  (coe←≡ʰ (Id′≡ A (SYM₂₀ δ) reflʰ reflʰ) (top₀₂ δ))
  (coe←≡ʰ (Id′≡ A (SYM₂₁ δ) reflʰ reflʰ) (top₁₂ δ)) (top₂₂ δ)
-}



SYM-SYM ε δ = reflᵉ
SYM-SYM (Δ ▸ A) δ = {!
  sq₂₂≡ A (SYM-SYM Δ (popsq δ))
    reflʰ
    reflʰ
    (coe←≡ʰ (Id′≡ A (SYM₀₂ (SYM Δ (popsq δ))) reflʰ reflʰ) (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
      •ʰ coe←≡ʰ (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ)
      •ʰ coe→≡ʰ (Id′-AP (_₀ {Δ}) (popsq δ) A _ _) (top (pop (pop (pop (pop (pop (pop δ))))))))
    reflʰ
    reflʰ
    (coe←≡ʰ (Id′≡ A (SYM₁₂ (SYM Δ (popsq δ))) reflʰ reflʰ) (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
      •ʰ coe←≡ʰ (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ)
      •ʰ coe→≡ʰ (Id′-AP≡ (λ x → (pop x) ₁) (popsq δ ∷ _ ∷ _ ∷ top (pop (pop (pop (pop (pop (pop δ))))))) (popsq δ ₁₂)
                (AP-AP (pop {B = λ x → A (x ₀)}) _₁ (popsq δ ∷ _ ∷ _ ∷ top (pop (pop (pop (pop (pop (pop δ))))))))
                A reflʰ reflʰ)
         (top (pop (pop (pop δ)))))
    (coe←≡ʰ (Id′≡ A (SYM₂₀ (SYM Δ (popsq δ)) reflʰ reflʰ)
            (unfrob₀₂ A (popsq δ) (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))))
      •ʰ coe→≡ʰ (Id′-AP (_₀ {Δ}) (popsq δ) A _ _) (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
      •ʰ coe←≡ʰ (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
    (coe←≡ʰ (Id′≡ A (SYM₂₁ (SYM Δ (popsq δ))) reflʰ reflʰ)
            (unfrob₁₂ A (popsq δ) (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
                                  (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ)))
      •ʰ coe→≡ʰ (Id′-AP≡ (λ x → (pop x) ₁) (popsq δ ∷ _ ∷ _ ∷ coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ)) (δ ₁₂)
                         (AP-AP (pop {B = λ x → A (x ₀)}) _₁ (popsq δ ∷ _ ∷ _ ∷ coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ)))
                         A reflʰ reflʰ)
                (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
      •ʰ coe←≡ʰ (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
    ?
  !}

{-
sq∷ A
      (SYM Δ
       (popsq
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (coe←
       (Id′≡ A
        (SYM₀₂
         (popsq
          (sq∷ A (SYM Δ (popsq δ))
           (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
           (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
           (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
           (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
           (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
            (top₂₂ δ)))))
        reflʰ reflʰ)
       (top₂₀
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (coe←
       (Id′≡ A
        (SYM₁₂
         (popsq
          (sq∷ A (SYM Δ (popsq δ))
           (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
           (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
           (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
           (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
           (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
            (top₂₂ δ)))))
        reflʰ reflʰ)
       (top₂₁
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (coe←
       (Id′≡ A
        (SYM₂₀
         (popsq
          (sq∷ A (SYM Δ (popsq δ))
           (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
           (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
           (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
           (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
           (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
            (top₂₂ δ)))))
        reflʰ reflʰ)
       (top₀₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (coe←
       (Id′≡ A
        (SYM₂₁
         (popsq
          (sq∷ A (SYM Δ (popsq δ))
           (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
           (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
           (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
           (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
           (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
            (top₂₂ δ)))))
        reflʰ reflʰ)
       (top₁₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      (sym A
       (popsq
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₀₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₁₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₂₀
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₂₁
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ))))
       (top₂₂
        (sq∷ A (SYM Δ (popsq δ))
         (coe← (Id′≡ A (SYM₀₂ (popsq δ)) reflʰ reflʰ) (top₂₀ δ))
         (coe← (Id′≡ A (SYM₁₂ (popsq δ)) reflʰ reflʰ) (top₂₁ δ))
         (coe← (Id′≡ A (SYM₂₀ (popsq δ)) reflʰ reflʰ) (top₀₂ δ))
         (coe← (Id′≡ A (SYM₂₁ (popsq δ)) reflʰ reflʰ) (top₁₂ δ))
         (sym A (popsq δ) (top₀₂ δ) (top₁₂ δ) (top₂₀ δ) (top₂₁ δ)
          (top₂₂ δ)))))
      ≡ δ
-}

-- {-# REWRITE sym-sym′ #-}
