{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --no-import-sorts --no-projection-like #-}

module HOTT.Square.Dependent where

open import HOTT.Base
open import HOTT.Id
open import HOTT.Universe
open import HOTT.Square.Simple

------------------------------
-- Dependent squares
------------------------------

record ∂2ᵈ {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁) (a₂₂ : Sq A a)
  (b₀₀ : B ∙ a₀₀) (b₀₁ : B ∙ a₀₁) (b₁₀ : B ∙ a₁₀) (b₁₁ : B ∙ a₁₁) : Typeᵉ where
  constructor ╔═_═╗_□_╚═_═╝
  infix 70 _₁₂ _₂₀ _₂₁ _₀₂
  field
    _₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁
    _₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀
    _₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁
    _₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁
open ∂2ᵈ public

Sqᵈ : {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁)
      (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                  a ₂₀   □    a ₂₁
                  └─    a ₀₂    ─┘)
      {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁} (b : ∂2ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) → Type
Sqᵈ {A} B {a₀₀} {a₀₁} {a₁₀} {a₁₁} a a₂₂ {b₀₀} {b₀₁} {b₁₀} {b₁₁} b =
  Id {ID× B} (Idᵈ B) {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁}
     (a ₀₂ , a ₁₂ , a₂₂ , b ₀₂ , b ₁₂) (b ₂₀) (b ₂₁)

-- Dependent boundaries in constant families are ordinary boundaries
←∂2ᵈ-const : {A B : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁}
  {a₂₂ : Sq A ┌─    a ₁₂    ─┐
              a ₂₀   □    a ₂₁
              └─    a ₀₂    ─┘}
  {b₀₀ b₀₁ b₁₀ b₁₁ : B} →
  ∂2ᵈ (ƛ _ ⇒ B) a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁ → ∂2 B b₀₀ b₀₁ b₁₀ b₁₁
←∂2ᵈ-const ╔═  b₁₂  ═╗
          b₂₀  □  b₂₁
          ╚═  b₀₂  ═╝ = ┌─  b₁₂  ─┐
                        b₂₀  □  b₂₁
                        └─  b₀₂  ─┘

-- Dependent squares in constant families are ordinary squares
←Sqᵈ-const :  {A : Type} (B : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁)
  (a₂₂ : Sq A ┌─    a ₁₂    ─┐
              a ₂₀   □    a ₂₁
              └─    a ₀₂    ─┘)
  {b₀₀ b₀₁ b₁₀ b₁₁ : B} (b : ∂2ᵈ (ƛ _ ⇒ B) a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
  Sqᵈ {A} (ƛ _ ⇒ B) ┌─   a ₁₂   ─┐
                    a ₂₀  □   a ₂₁
                    └─   a ₀₂   ─┘  a₂₂  ╔═   b ₁₂  ═╗
                                         b ₂₀  □  b ₂₁
                                         ╚═   b ₀₂  ═╝ →
  Sq B ┌─   b ₁₂  ─┐
       b ₂₀  □  b ₂₁
       └─   b ₀₂  ─┘
←Sqᵈ-const {A} B {a₀₀} {a₀₁} {a₁₀} {a₁₁} a a₂₂ {b₀₀} {b₀₁} {b₁₀} {b₁₁} b b₂₂ =
  ←Id-ap {（ a₀ ⦂ A ）× （ a₁ ⦂ A ）× （ a₂ ⦂ a₀ ＝ a₁ ）× B × B} {B × B}
         (λ u → snd (snd (snd u))) (ƛ u ⇒ fst u ＝ snd u)
         {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁}
         (a ₀₂ , a ₁₂ , a₂₂ , b ₀₂ , b ₁₂) b₂₂

→Sqᵈ-const :  {A : Type} (B : Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁)
  (a₂₂ : Sq A ┌─    a ₁₂    ─┐
              a ₂₀   □    a ₂₁
              └─    a ₀₂    ─┘)
  {b₀₀ b₀₁ b₁₀ b₁₁ : B} (b : ∂2ᵈ (ƛ _ ⇒ B) a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
  Sq B ┌─   b ₁₂  ─┐
       b ₂₀  □  b ₂₁
       └─   b ₀₂  ─┘ →
  Sqᵈ {A} (ƛ _ ⇒ B) ┌─   a ₁₂   ─┐
                    a ₂₀  □   a ₂₁
                    └─   a ₀₂   ─┘  a₂₂  ╔═   b ₁₂  ═╗
                                         b ₂₀  □  b ₂₁
                                         ╚═   b ₀₂  ═╝
→Sqᵈ-const {A} B {a₀₀} {a₀₁} {a₁₀} {a₁₁} a a₂₂ {b₀₀} {b₀₁} {b₁₀} {b₁₁} b b₂₂ =
  →Id-ap {（ a₀ ⦂ A ）× （ a₁ ⦂ A ）× （ a₂ ⦂ a₀ ＝ a₁ ）× B × B} {B × B}
         (λ u → snd (snd (snd u))) (ƛ u ⇒ fst u ＝ snd u)
         {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁}
         (a ₀₂ , a ₁₂ , a₂₂ , b ₀₂ , b ₁₂) b₂₂

-- Dependent boundaries over refl-refl are ordinary boundaries
←∂2ᵈ-refl : {A : Type} (B : A ⇒ Type) (a : A) {b₀₀ b₀₁ b₁₀ b₁₁ : B ∙ a} →
  ∂2ᵈ B (refl-∂2 a) (refl (refl a)) b₀₀ b₀₁ b₁₀ b₁₁ →
  ∂2 (B ∙ a) b₀₀ b₀₁ b₁₀ b₁₁
←∂2ᵈ-refl B a ╔═  b₁₂  ═╗
             b₂₀  □  b₂₁
             ╚═  b₀₂  ═╝ = ┌─  b₁₂  ─┐
                           b₂₀  □  b₂₁
                           └─  b₀₂  ─┘

-- Dependent squares over refl-refl are ordinary squares.  This holds
-- definitionally even without nudging!
{-
←Sqᵈ-refl : {A : Type} (B : A ⇒ Type) {a : A} {b₀₀ b₀₁ b₁₀ b₁₁ : B ∙ a}
  (b : ∂2ᵈ B (refl-∂2 a) (refl (refl a)) b₀₀ b₀₁ b₁₀ b₁₁) →
  Sqᵈ B ┌─    refl a   ─┐
        refl a  □  refl a
        └─    refl a   ─┘  (refl (refl a))   ╔═   b ₁₂  ═╗
                                             b ₂₀  □  b ₂₁
                                             ╚═   b ₀₂  ═╝ →
  Sq (B ∙ a) ┌─   b ₁₂  ─┐
             b ₂₀  □  b ₂₁
             └─   b ₀₂  ─┘
←Sqᵈ-refl {A} B {a} {b₀₀} {b₀₁} {b₁₀} {b₁₁} b b₂₂ = b₂₂
-}

------------------------------
-- Dependent symmetry
------------------------------

postulate
  symᵈ : {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                a ₂₀   □    a ₂₁
                └─    a ₀₂    ─┘)
    {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁}
    (b : ∂2ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
    Sqᵈ B ┌─   a ₁₂   ─┐
          a ₂₀  □   a ₂₁
          └─   a ₀₂   ─┘     a₂₂       ╔═   b ₁₂  ═╗
                                       b ₂₀  □  b ₂₁
                                       ╚═   b ₀₂  ═╝ →
    Sqᵈ B ┌─   a ₂₁   ─┐
          a ₀₂  □   a ₁₂
          └─   a ₂₀   ─┘ (sym A a a₂₂) ╔═   b ₂₁  ═╗
                                       b ₀₂  □  b ₁₂
                                       ╚═   b ₂₀  ═╝

sym-∂2ᵈ : {A : Type} {B : A ⇒ Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁}
    {a₂₂ : Sq A ┌─    a ₁₂    ─┐
                a ₂₀   □    a ₂₁
                └─    a ₀₂    ─┘}
    {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁} →
    ∂2ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁ → ∂2ᵈ B (sym-∂2 a) (sym A a a₂₂) b₀₀ b₁₀ b₀₁ b₁₁
sym-∂2ᵈ ╔═  b₁₂  ═╗
       b₂₀  □  b₂₁
       ╚═  b₀₂  ═╝ = ╔═  b₂₁  ═╗
                     b₀₂  □  b₁₂
                     ╚═  b₂₀  ═╝

postulate
  sym-symᵈ : {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                a ₂₀   □    a ₂₁
                └─    a ₀₂    ─┘)
    {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁}
    (b : ∂2ᵈ B a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
    (b₂₂ : Sqᵈ B ┌─   a ₁₂   ─┐
                 a ₂₀  □   a ₂₁
                 └─   a ₀₂   ─┘  a₂₂  ╔═   b ₁₂  ═╗
                                      b ₂₀  □  b ₂₁
                                      ╚═   b ₀₂  ═╝) →
    symᵈ B (sym-∂2 a) (sym A a a₂₂) (sym-∂2ᵈ b) (symᵈ B a a₂₂ b b₂₂) ≡ b₂₂
{-# REWRITE sym-symᵈ #-}

postulate
  symᵈ-const : {A B : Type} {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁)
    (a₂₂ : Sq A ┌─    a ₁₂    ─┐
                a ₂₀   □    a ₂₁
                └─    a ₀₂    ─┘)
    {b₀₀ b₀₁ b₁₀ b₁₁ : B} (b : ∂2ᵈ (ƛ _ ⇒ B) a a₂₂ b₀₀ b₀₁ b₁₀ b₁₁) →
    (b₂₂ : Sqᵈ {A} (ƛ _ ⇒ B) ┌─   a ₁₂   ─┐
                             a ₂₀  □   a ₂₁
                             └─   a ₀₂   ─┘  a₂₂  ╔═   b ₁₂  ═╗
                                                  b ₂₀  □  b ₂₁
                                                  ╚═   b ₀₂  ═╝) →
    symᵈ (ƛ _ ⇒ B) a a₂₂ b b₂₂ ≡
    →Sqᵈ-const B (sym-∂2 a) (sym A a a₂₂) (sym-∂2ᵈ b)
      (sym B (←∂2ᵈ-const b) (←Sqᵈ-const B a a₂₂ b b₂₂))
{-# REWRITE symᵈ-const #-}

postulate
  symᵈ-refl : {A : Type} (B : A ⇒ Type) (a : A) {b₀₀ b₀₁ b₁₀ b₁₁ : B ∙ a}
    (b : ∂2ᵈ B (refl-∂2 a) (refl (refl a)) b₀₀ b₀₁ b₁₀ b₁₁) →
    (b₂₂ : Sqᵈ B ┌─    refl a   ─┐
                 refl a  □  refl a
                 └─    refl a   ─┘  (refl (refl a))   ╔═   b ₁₂  ═╗
                                                      b ₂₀  □  b ₂₁
                                                      ╚═   b ₀₂  ═╝) →
    symᵈ B (refl-∂2 a) (refl (refl a)) b b₂₂ ≡
    sym (B ∙ a) (←∂2ᵈ-refl B a b) b₂₂
{-# REWRITE symᵈ-refl #-}

----------------------------------------
-- Dependent composition and filling
----------------------------------------

module _ {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁)
  (a₂₂ : Sq A ┌─    a ₁₂    ─┐
              a ₂₀   □    a ₂₁
              └─    a ₀₂    ─┘)
  {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁} where 

  compᵈ→ : (b₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁) (b₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁) (b₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀) →
    Id (B ∙_) (a ₂₁) b₀₁ b₁₁
  compᵈ→ b₀₂ b₁₂ b₂₀ =
    tr⇒ (Idᵈ B) {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁} (a ₀₂ , a ₁₂ , a₂₂ , b₀₂ , b₁₂) ∙ b₂₀

  fillᵈ→ : (b₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁) (b₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁) (b₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀) →
    Sqᵈ B a a₂₂ ╔═   b₁₂  ═╗
                b₂₀   □  compᵈ→ b₀₂ b₁₂ b₂₀
                ╚═   b₀₂  ═╝
  fillᵈ→ b₀₂ b₁₂ b₂₀ =
    lift⇒ (Idᵈ B) {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁} (a ₀₂ , a ₁₂ , a₂₂ , b₀₂ , b₁₂) ∙ b₂₀

  compᵈ← : (b₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁) (b₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁) (b₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁) →
    Id (B ∙_) (a ₂₀) b₀₀ b₁₀
  compᵈ← b₀₂ b₁₂ b₂₁ =
    tr⇐ (Idᵈ B) {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁} (a ₀₂ , a ₁₂ , a₂₂ , b₀₂ , b₁₂) ∙ b₂₁

  fillᵈ← : (b₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁) (b₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁) (b₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁) →
    Sqᵈ B a a₂₂        ╔═           b₁₂  ═╗
                compᵈ← b₀₂ b₁₂ b₂₁   □  b₂₁
                       ╚═           b₀₂  ═╝
  fillᵈ← b₀₂ b₁₂ b₂₁ =
    lift⇐ (Idᵈ B) {a₀₀ , a₁₀ , a ₂₀ , b₀₀ , b₁₀} {a₀₁ , a₁₁ , a ₂₁ , b₀₁ , b₁₁} (a ₀₂ , a ₁₂ , a₂₂ , b₀₂ , b₁₂) ∙ b₂₁

module _ {A : Type} (B : A ⇒ Type) {a₀₀ a₀₁ a₁₀ a₁₁ : A} (a : ∂2 A a₀₀ a₀₁ a₁₀ a₁₁)
  (a₂₂ : Sq A ┌─    a ₁₂    ─┐
              a ₂₀   □    a ₂₁
              └─    a ₀₂    ─┘)
  {b₀₀ : B ∙ a₀₀} {b₀₁ : B ∙ a₀₁} {b₁₀ : B ∙ a₁₀} {b₁₁ : B ∙ a₁₁} where 

  compᵈ↑ : (b₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁) (b₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀) (b₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁) →
    Id (B ∙_) (a ₁₂) b₁₀ b₁₁
  compᵈ↑ b₀₂ b₂₀ b₂₁ = compᵈ→ B (sym-∂2 a) (sym A a a₂₂) b₂₀ b₂₁ b₀₂

  fillᵈ↑ : (b₀₂ : Id (B ∙_) (a ₀₂) b₀₀ b₀₁) (b₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀) (b₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁) →
    Sqᵈ B a a₂₂ ╔═  compᵈ↑ b₀₂ b₂₀ b₂₁  ═╗
                b₂₀          □         b₂₁
                ╚═          b₀₂         ═╝
  fillᵈ↑ b₀₂ b₂₀ b₂₁ = symᵈ B (sym-∂2 a) (sym A a a₂₂) ╔═   b₂₁  ═╗
                                                      b₀₂   □  compᵈ↑ b₀₂ b₂₀ b₂₁
                                                      ╚═   b₂₀  ═╝
                             (fillᵈ→ B (sym-∂2 a) (sym A a a₂₂) b₂₀ b₂₁ b₀₂)

  compᵈ↓ : (b₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁) (b₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀) (b₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁) →
    Id (B ∙_) (a ₀₂) b₀₀ b₀₁
  compᵈ↓ b₁₂ b₂₀ b₂₁ = compᵈ← B (sym-∂2 a) (sym A a a₂₂) b₂₀ b₂₁ b₁₂

  fillᵈ↓ : (b₁₂ : Id (B ∙_) (a ₁₂) b₁₀ b₁₁) (b₂₀ : Id (B ∙_) (a ₂₀) b₀₀ b₁₀) (b₂₁ : Id (B ∙_) (a ₂₁) b₀₁ b₁₁) →
    Sqᵈ B a a₂₂ ╔═          b₁₂         ═╗
                b₂₀          □         b₂₁
                ╚═  compᵈ↓ b₁₂ b₂₀ b₂₁  ═╝
  fillᵈ↓ b₁₂ b₂₀ b₂₁ = symᵈ B (sym-∂2 a) (sym A a a₂₂)         ╔═         b₂₁  ═╗
                                                      compᵈ↓ b₁₂ b₂₀ b₂₁  □  b₁₂
                                                              ╚═         b₂₀  ═╝
                             (fillᵈ← B (sym-∂2 a) (sym A a a₂₂) b₂₀ b₂₁ b₁₂)
