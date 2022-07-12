{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --experimental-lossy-unification --no-import-sorts #-}

module HOTT.Groupoids where

open import HOTT.Rewrite using (Type; _≡_; _≡ᵉ_; coe→; coe←)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Square.EpBoundary
open import HOTT.Sym.Base
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Sigma.Base
open import HOTT.Sigma.Transport

infixl 40 _⊙_
infix 35 _≋_

------------------------------
-- Path operations
------------------------------

_⊙_ : {A : Type} {x y z : A} (p : x ＝ y) (q : y ＝ z) → x ＝ z
_⊙_ {A} {x} {y} {z} p q = comp→ {ε} (Λ _ ⇨ A) [] {x} {x} (refl x) {y} {z} q p

rev : {A : Type} {x y : A} (p : x ＝ y) → (y ＝ x)
rev {A} {x} {y} p = comp→ {ε} (Λ _ ⇨ A) [] {x} {y} p {x} {x} (refl x) (refl x)

cong : {A B : Type} (f : A ⇒ B) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → (f ∙ a₀ ＝ f ∙ a₁)
cong f {a₀} {a₁} a₂ = refl f ∙ a₀ ∙ a₁ ∙ a₂

happly : {A B : Type} {f g : A ⇒ B} (H : f ＝ g) (a : A) → f ∙ a ＝ g ∙ a
happly H a = H ∙ a ∙ a ∙ refl a

tr⇒ : {A : Type} (B : A ⇒ Type) {x y : A} (p : x ＝ y) (b : B ∙ x) → B ∙ y
tr⇒ {A} B {x} {y} p b = tr→ {ε▸ A} (Λ x ⇨ B ∙ top x) ([] ∷ x ∷ y ∷ p) b

tr⇐ : {A : Type} (B : A ⇒ Type) {x y : A} (p : x ＝ y) (b : B ∙ y) → B ∙ x
tr⇐ {A} B {x} {y} p b = tr← {ε▸ A} (Λ x ⇨ B ∙ top x) ([] ∷ x ∷ y ∷ p) b

-- In deducing the typal computation rule for 𝐉, the central lemma is
-- that transporting along anything equal to refl is the identity.
-- Note that we can prove this with utr→ without using symmetry,
-- although comp↑ (which was defined using symmetry) would also work.
tr⇒refl : {A : Type} (B : A ⇒ Type) (a : A) (b : B ∙ a) →
  tr⇒ B (refl a) b ＝ b
tr⇒refl {A} B a b = utr→ {ε▸ A} (Λ x ⇨ B ∙ top x) ([] ∷ a ∷ a ∷ refl a) b (tr⇒ B (refl a) b) b
                         (lift→ {ε▸ A} (Λ x ⇨ B ∙ top x) ([] ∷ a ∷ a ∷ refl a) b) (refl b)

tr⇒＝refl : (A : Type) (B : A ⇒ Type) (a : A) (a₂ : a ＝ a) (a₂＝refl : a₂ ＝ refl a) (b : B ∙ a) →
  tr⇒ B a₂ b ＝ b
tr⇒＝refl A B a a₂ a₂＝refl b = cong (ƛ p ⇒ tr⇒ B p b) a₂＝refl ⊙ tr⇒refl B a b

-- An analogous argument implies one of the unit laws for concatenation.
⊙refl : {A : Type} {x y : A} (p : x ＝ y) → (p ⊙ refl y ＝ p)
⊙refl {A} {x} {y} p =
  utr→ {ε▸ A ▸ ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))}
       (Λ z ⇨ top (pop z) ＝ top z) ([] ∷ x ∷ x ∷ refl x ∷ y ∷ y ∷ refl y) p
       (tr→ {ε▸ A ▸ ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))}
            (Λ z ⇨ top (pop z) ＝ top z) ([] ∷ x ∷ x ∷ refl x ∷ y ∷ y ∷ refl y) p)
       p
       (lift→ {ε▸ A ▸ ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))}
            (Λ z ⇨ top (pop z) ＝ top z) ([] ∷ x ∷ x ∷ refl x ∷ y ∷ y ∷ refl y) p)
       (coe← (Id-REFL▸▸ {ε} (Λ _ ⇨ A) ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))
                         (Λ z ⇨ top (pop z) ＝ top z) [] x y p p)
             (refl p))

-- And that refl is its own inverse.
rev-refl : {A : Type} (x : A) → rev (refl x) ＝ refl x
rev-refl {A} x =
  utr→ {ε▸ A ▸ ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))}
        (Λ z ⇨ top (pop z) ＝ top z) ([] ∷ x ∷ x ∷ refl x ∷ x ∷ x ∷ refl x)
        (refl x)
        (tr→ {ε▸ A ▸ ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))}
             (Λ z ⇨ top (pop z) ＝ top z) ([] ∷ x ∷ x ∷ refl x ∷ x ∷ x ∷ refl x) (refl x))
        (refl x)
        (lift→ {ε▸ A ▸ ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))}
               (Λ z ⇨ top (pop z) ＝ top z) ([] ∷ x ∷ x ∷ refl x ∷ x ∷ x ∷ refl x) (refl x))
        (coe← (Id-REFL▸▸ {ε} (Λ _ ⇨ A) ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))
                         (Λ z ⇨ top (pop z) ＝ top z) [] x x (refl x) (refl x))
               (refl (refl x)))

------------------------------
-- Equational reasoning
------------------------------

infix  1 begin_
infixr 2 _＝⟨⟩_ _＝⟨_⟩_
infix  3 _∎

data _＝′_ {A : Type} : A → A → Type where
  _∎ : (a : A) → a ＝′ a
  _＝⟨⟩_ : (x : A) {y : A} → (x ＝′ y) → (x ＝′ y)
  _＝⟨_⟩_ : (x : A) {y z : A} → (x ＝ y) → (y ＝′ z) → (x ＝′ z)

begin_ : {A : Type} {x y : A} → (x ＝′ y) → (x ＝ y)
begin x ∎ = refl x
begin x ＝⟨⟩ p = begin p
begin_ {A} (x ＝⟨ p ⟩ q) = _⊙_ {A} p (begin q)

--------------------------------------------------
-- Propositions and contractibility
--------------------------------------------------

-- We define propositions first, as subsingletons: any two points are equal.
isProp : (A : Type) → Type
isProp A = Π A (λ a₀ → Π A (λ a₁ → (a₀ ＝ a₁)))

-- The product of two propositions is a proposition.
isProp-× : {A B : Type} → isProp A → isProp B → isProp (A × B)
isProp-× p q = ƛ x ⇒ ƛ y ⇒ (p ∙ fst x ∙ fst y , q ∙ snd x ∙ snd y)

-- We define a contractible types to be inhabited propositions.
isContr : (A : Type) → Type
isContr A = A × isProp A

-- The product of two contractible types is contractible.
isContr-× : {A B : Type} → isContr A → isContr B → isContr (A × B)
isContr-× (a , p) (b , q) = ((a , b) , isProp-× p q)

-- Based path-spaces (singletons) are contractible.
isProp-sing→ : {A : Type} (a : A) → isProp (Σ[ y ⦂ A ] a ＝ y)
isProp-sing→ {A} a = (ƛ x ⇒ ƛ y ⇒ utr→ (Λ _ ⇨ A) [] a (fst x) (fst y) (snd x) (snd y) ,
                                ulift→ (Λ _ ⇨ A) [] a (fst x) (fst y) (snd x) (snd y))

isContr-sing→ : {A : Type} (a : A) → isContr (Σ[ y ⦂ A ] a ＝ y)
isContr-sing→ {A} a = ((a , refl a) , isProp-sing→ a)

isProp-sing← : {A : Type} (a : A) → isProp (Σ[ x ⦂ A ] x ＝ a)
isProp-sing← {A} a = (ƛ x ⇒ ƛ y ⇒ utr← (Λ _ ⇨ A) [] a (fst x) (fst y) (snd x) (snd y) ,
                                ulift← (Λ _ ⇨ A) [] a (fst x) (fst y) (snd x) (snd y))

isContr-sing← : {A : Type} (a : A) → isContr (Σ[ x ⦂ A ] x ＝ a)
isContr-sing← {A} a = ((a , refl a) , isProp-sing← a)

-- The central nontrivial fact about h-levels: the identity types of a
-- proposition are propositions.  Note that it uses symmetry and also
-- utr→ (although comp↑ ought to work as well as utr→).
isProp-＝ : {A : Type} (prp : isProp A) (a b : A) → isProp (a ＝ b)
isProp-＝ {A} prp a b = ƛ p ⇒ ƛ q ⇒
  utr→ (Id/ {ε} (Λ _ ⇨ A)) ([] ∷ a ∷ a ∷ (prp ∙ a ∙ a) ∷ a ∷ b ∷ (prp ∙ a ∙ b)) (refl a) p q
  (sym (Λ _ ⇨ A) [] (refl a) p (prp ∙ a ∙ a) (prp ∙ a ∙ b)
    (coe→ (Id-AP {ε▸ A} {ε▸ A ▸ ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))}
                 (λ x → [] ∷ a ∷ top x) ([] ∷ a ∷ b ∷ p) (Λ x ⇨ top (pop x) ＝ top x) (prp ∙ a ∙ a) (prp ∙ a ∙ b))
          (refl (prp ∙ a) ∙ a ∙ b ∙ p)))
  (sym (Λ _ ⇨ A) [] (refl a) q (prp ∙ a ∙ a) (prp ∙ a ∙ b)
    (coe→ (Id-AP {ε▸ A} {ε▸ A ▸ ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))}
                 (λ x → [] ∷ a ∷ top x) ([] ∷ a ∷ b ∷ q) (Λ x ⇨ top (pop x) ＝ top x) (prp ∙ a ∙ a) (prp ∙ a ∙ b))
          (refl (prp ∙ a) ∙ a ∙ b ∙ q)))

-- This implies that the identity types of a proposition are in fact contractible.
isContr-＝ : {A : Type} (cA : isProp A) (a b : A) → isContr (a ＝ b)
isContr-＝ {A} prp a b =
  (prp ∙ a ∙ b , isProp-＝ prp a b)

-- A set is a type whose identity types are propositions.
isSet : (A : Type) → Type
isSet A = Π[ x ⦂ A ] Π[ y ⦂ A ] isProp (x ＝ y)

-- Another way of saying isProp-＝ is that any proposition is a set.
isProp→isSet : {A : Type} (pA : isProp A) → isSet A
isProp→isSet {A} pA = ƛ x ⇒ ƛ y ⇒ isProp-＝ pA x y

-- The type of all propositions, and the type of all sets.
Prop : Type
Prop = Σ[ P ⦂ Type ] isProp P

Set : Type
Set = Σ[ A ⦂ Type ] isSet A

------------------------------
-- Identity elimination
------------------------------

-- As in cubical type theory, the identity eliminator is defined by
-- transporting across contractibility of the based path-space.
𝐉 : {A : Type} {a : A} (P : (x : A) → (a ＝ x) → Type) (d : P a (refl a))
  (x : A) (e : a ＝ x) → P x e
𝐉 {A} {a} P d x e = tr⇒ (ƛ z ⇒ P (fst z) (snd z)) (isProp-sing→ a ∙ (a , refl a) ∙ (x , e)) d

-- This proof is, again, just like in cubical type theory.
𝐉β : {A : Type} {a : A} (P : (x : A) → (a ＝ x) → Type) (d : P a (refl a)) →
  𝐉 P d a (refl a) ＝ d
𝐉β {A} {a} P d =
  tr⇒＝refl (Σ[ x ⦂ A ] a ＝ x) (ƛ z ⇒ P (fst z) (snd z)) (a , refl a) _
    (isProp-＝ (isProp-sing→ a) (a , refl a) (a , refl a) ∙
      (isProp-sing→ a ∙ (a , refl a) ∙ (a , refl a)) ∙ (refl (a , refl a)) ) d

------------------------------
-- Groupoid laws
------------------------------

-- With 𝐉 and ⊙refl and rev-refl, we can derive the other groupoid laws.

refl⊙ : {A : Type} {x y : A} (p : x ＝ y) → (refl x ⊙ p ＝ p)
refl⊙ {A} {x} {y} p = 𝐉 (λ z q → refl x ⊙ q ＝ q) (⊙refl (refl x)) y p

⊙assoc : {A : Type} {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
  (p ⊙ q) ⊙ r ＝ p ⊙ (q ⊙ r)
⊙assoc {A} {x} {y} {z} {w} p q r =
  𝐉 (λ w r → (p ⊙ q) ⊙ r ＝ p ⊙ (q ⊙ r)) (⊙refl (p ⊙ q) ⊙ cong (ƛ s ⇒ p ⊙ s) (rev (⊙refl q))) w r

⊙rev : {A : Type} {x y : A} (p : x ＝ y) → (p ⊙ rev p ＝ refl x)
⊙rev {A} {x} {y} p =
  𝐉 (λ y p → p ⊙ rev p ＝ refl x) (cong (ƛ q ⇒ refl x ⊙ q) (rev-refl x) ⊙ ⊙refl (refl x)) y p

rev⊙ : {A : Type} {x y : A} (p : x ＝ y) → (rev p ⊙ p ＝ refl y)
rev⊙ {A} {x} {y} p =
  𝐉 (λ y p → rev p ⊙ p ＝ refl y) (cong (ƛ q ⇒ q ⊙ refl x) (rev-refl x) ⊙ ⊙refl (refl x)) y p

-- Also we can prove naive funext.
funext : {A B : Type} {f g : A ⇒ B} (p : Π[ x ⦂ A ] f ∙ x ＝ g ∙ x) → (f ＝ g)
funext {A} {B} {f} {g} p = ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ 𝐉 (λ a₁ a₂ → f ∙ a₀ ＝ g ∙ a₁) (p ∙ a₀) a₁ a₂

------------------------------
-- isProp-isProp
------------------------------

-- A version of isProp-＝ for dependent identity types
isProp-Id : {A : Type} {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (B : A → Type)
  (prp : (x : A) → isProp (B x)) (b₀ : B a₀) (b₁ : B a₁) →
  isProp (Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁)
isProp-Id {A} {a₀} {a₁} a₂ B prp b₀ b₁ =
   𝐉 (λ a₁ a₂ → (b₁ : B a₁) → isProp (Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁))
     (λ b₁' → isProp-＝ (prp a₀) b₀ b₁') a₁ a₂ b₁

Id-prop : {A : Type} {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (B : A → Type)
  (prp : (x : A) → isProp (B x)) (b₀ : B a₀) (b₁ : B a₁) →
  Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁
Id-prop {A} {a₀} {a₁} a₂ B prp b₀ b₁ =
   𝐉 (λ a₁ a₂ → (b₁ : B a₁) → Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁)
     (λ b₁' → prp a₀ ∙ b₀ ∙ b₁') a₁ a₂ b₁

isContr-Id : {A : Type} {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (B : A → Type)
  (prp : (x : A) → isProp (B x)) (b₀ : B a₀) (b₁ : B a₁) →
  isContr (Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁)
isContr-Id {A} {a₀} {a₁} a₂ B prp b₀ b₁ =
   (Id-prop a₂ B prp b₀ b₁ , isProp-Id a₂ B prp b₀ b₁)

-- Also, any square in a family of propositions can be filled.
{-
sq-isProp : {Δ : Tel} (A : Δ ⇨ Type) (prp : (x : el Δ) → isProp (A ⊘ x)) (δ : el (SQ Δ))
  {a₀₀ : A ⊘ (δ ₀₀)} {a₀₁ : A ⊘ (δ ₀₁)} (a₀₂ : Id A (δ ₀₂) a₀₀ a₀₁)
  {a₁₀ : A ⊘ (δ ₁₀)} {a₁₁ : A ⊘ (δ ₁₁)} (a₁₂ : Id A (δ ₁₂) a₁₀ a₁₁)
  (a₂₀ : Id A (δ ₂₀) a₀₀ a₁₀) (a₂₁ : Id A (δ ₂₁) a₀₁ a₁₁) →
  Sq A δ a₀₂ a₁₂ a₂₀ a₂₁
sq-isProp A prp δ a₀₂ a₁₂ a₂₀ a₂₁ = {!!}
-}

-- Being a proposition is a proposition
{-
isProp-isProp : (A : Type) → isProp (isProp A)
isProp-isProp A = ƛ prp₀ ⇒ ƛ prp₁ ⇒
  ƛ a₀₀ ⇒ ƛ a₀₁ ⇒ ƛ a₀₂ ⇒ ƛ a₁₀ ⇒ ƛ a₁₁ ⇒ ƛ a₁₂ ⇒
  {! sq-isProp {ε} (Λ _ ⇨ A) (λ _ → prp₀) [] a₀₂ a₁₂ (prp₀ ∙ a₀₀ ∙ a₁₀) (prp₁ ∙ a₀₁ ∙ a₁₁) !}
-}

------------------------------
-- 1-1 correspondences
------------------------------

is11 : {A B : Type} (R : A ⇒ B ⇒ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⇒ B ⇒ Type) is11

----------------------------------------
-- Quasi-invertible maps
----------------------------------------

QInv : {A B : Type} (f : A ⇒ B) → Type
QInv {A} {B} f = Σ[ g ⦂ B ⇒ A ] (g ∘ f ＝ idmap A) × (f ∘ g ＝ idmap B)

_≋_ : Type → Type → Type
A ≋ B = Σ[ f ⦂ A ⇒ B ] QInv f

-- We will prove any quasi-invertible map yields a 1-1 correspondence.
-- One approach to this result is to "adjointify" a quasi-inverse to a
-- half-adjoint equivalence, and use the triangle identities in
-- showing that the desired correspondence is 1-1.  We will instead
-- take a more roundabout route, by way of a bunch of abstract but
-- fairly straightforward categorical properties about quasi-inverses.
-- This may be longer, but it avoids reasoning with 2D paths.

-- Throughout, we must resist the temptation to decompose elements of
-- QInv by pattern-matching on the left side of a definition, as this
-- breaks reduction in cases where the quasi-inverse is not concrete.

-- We first show that quasi-inverses satisfy the 2-out-of-3 property.

∘QInv : {A B C : Type} (f : A ⇒ B) (qf : QInv f) (g : B ⇒ C) (qg : QInv g) → QInv (g ∘ f)
∘QInv f qf g qg =
  let f⁻¹ = fst qf
      fsect = fst (snd qf)
      fretr = snd (snd qf) in
  let g⁻¹ = fst qg
      gsect = fst (snd qg)
      gretr = snd (snd qg) in
  f⁻¹ ∘ g⁻¹ ,
  funext (ƛ x ⇒ cong f⁻¹ (happly gsect (f ∙ x)) ⊙ happly fsect x) ,
  funext (ƛ y ⇒ cong g (happly fretr (g⁻¹ ∙ y)) ⊙ happly gretr y)

∘QInv-cancelR : {A B C : Type} (f : A ⇒ B) (qf : QInv f) (g : B ⇒ C) (qgf : QInv (g ∘ f)) → QInv g
∘QInv-cancelR f qf g qgf =
  let gf⁻¹ = fst qgf
      gfsect = fst (snd qgf)
      gfretr = snd (snd qgf) in
  let f⁻¹ = fst qf
      fsect = fst (snd qf)
      fretr = snd (snd qf) in
  (ƛ z ⇒ f ∙ (gf⁻¹ ∙ z)) ,
  funext (ƛ y ⇒ (begin
                   f ∙ (gf⁻¹ ∙ (g ∙ y))
                 ＝⟨ cong (f ∘ gf⁻¹ ∘ g) (rev (happly fretr y)) ⟩
                   f ∙ (gf⁻¹ ∙ (g ∙ (f ∙ (f⁻¹ ∙ y))))
                 ＝⟨ cong f (happly gfsect (f⁻¹ ∙ y)) ⟩
                   f ∙ (f⁻¹ ∙ y)
                 ＝⟨ happly fretr y ⟩
                   y
                 ∎)) ,
  funext (ƛ z ⇒ happly gfretr z)

∘QInv-cancelL : {A B C : Type} (f : A ⇒ B) (g : B ⇒ C) (qg : QInv g) (qgf : QInv (g ∘ f)) → QInv f
∘QInv-cancelL f g qg qgf =
  let gf⁻¹ = fst qgf
      gfsect = fst (snd qgf)
      gfretr = snd (snd qgf) in
  let g⁻¹ = fst qg
      gsect = fst (snd qg)
      gretr = snd (snd qg) in
  (ƛ y ⇒ gf⁻¹ ∙ (g ∙ y)) ,
  funext (ƛ x ⇒ happly gfsect x) ,
  funext (ƛ y ⇒ (begin
                   f ∙ (gf⁻¹ ∙ (g ∙ y))
                 ＝⟨ rev (happly gsect (f ∙ (gf⁻¹ ∙ (g ∙ y)))) ⟩
                   g⁻¹ ∙ (g ∙ (f ∙ (gf⁻¹ ∙ (g ∙ y))))
                 ＝⟨ cong g⁻¹ (happly gfretr (g ∙ y)) ⟩
                   g⁻¹ ∙ (g ∙ y)
                 ＝⟨ happly gsect y ⟩
                   y
                 ∎))

-- Similarly, they satisfy the 2-out-of-6 property.  We will only need
-- 1/4 of the full 2-out-of-6 property.
∘QInv-2/6 : {A B C D : Type} (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D)
  (qgf : QInv (g ∘ f)) (qhg : QInv (h ∘ g)) →
  QInv f
∘QInv-2/6 f g h qgf qhg =
  let gf⁻¹ = fst qgf
      gfsect = fst (snd qgf)
      gfretr = snd (snd qgf) in
  let hg⁻¹ = fst qhg
      hgsect = fst (snd qhg)
      hgretr = snd (snd qhg) in
  (ƛ y ⇒ gf⁻¹ ∙ (g ∙ y)) ,
  funext (ƛ x ⇒ happly gfsect x) ,
  funext (ƛ y ⇒ (begin
                   f ∙ (gf⁻¹ ∙ (g ∙ y))
                 ＝⟨ rev (happly hgsect _) ⟩
                   hg⁻¹ ∙ (h ∙ (g ∙ (f ∙ (gf⁻¹ ∙ (g ∙ y)))))
                 ＝⟨ cong (hg⁻¹ ∘ h) (happly gfretr (g ∙ y)) ⟩
                   hg⁻¹ ∙ (h ∙ (g ∙ y))
                 ＝⟨ happly hgsect y ⟩
                   y
                 ∎))

-- Concatenating identifications on either side is quasi-invertible,
-- since you can concatenate with the reverse.
⊙QInvR : {A : Type} (x : A) {y z : A} (q : y ＝ z) → QInv (ƛ p ⇒ _⊙_ {A} {x} p q)
⊙QInvR x {y} {z} q = (ƛ r ⇒ r ⊙ rev q) ,
  funext (ƛ p ⇒ (begin
                   (p ⊙ q) ⊙ rev q
                 ＝⟨ ⊙assoc p q (rev q) ⟩
                   p ⊙ (q ⊙ rev q)
                 ＝⟨ cong (ƛ r ⇒ p ⊙ r) (⊙rev q) ⟩
                   p ⊙ refl y
                 ＝⟨ ⊙refl p ⟩
                   p
                 ∎)) ,
  funext (ƛ r ⇒ (begin
                   (r ⊙ rev q) ⊙ q
                 ＝⟨ ⊙assoc r (rev q) q ⟩
                   r ⊙ (rev q ⊙ q)
                 ＝⟨ cong (ƛ p ⇒ r ⊙ p) (rev⊙ q) ⟩
                   r ⊙ refl z
                 ＝⟨ ⊙refl r ⟩
                   r
                 ∎))

⊙QInvL : {A : Type} {x y : A} (z : A) (p : x ＝ y) → QInv (ƛ q ⇒ _⊙_ {A} {x} {y} {z} p q)
⊙QInvL {A} {x} {y} z p = (ƛ r ⇒ rev p ⊙ r) ,
  funext (ƛ q ⇒ (begin
                   rev p ⊙ (p ⊙ q)
                 ＝⟨ rev (⊙assoc (rev p) p q) ⟩
                   (rev p ⊙ p) ⊙ q
                 ＝⟨ cong (ƛ r ⇒ r ⊙ q) (rev⊙ p) ⟩
                   refl _ ⊙ q
                 ＝⟨ refl⊙ q ⟩
                   q
                 ∎)) ,
  funext (ƛ r ⇒ (begin
                   p ⊙ (rev p ⊙ r)
                 ＝⟨ rev (⊙assoc p (rev p) r) ⟩
                   (p ⊙ rev p) ⊙ r
                 ＝⟨ cong (ƛ q ⇒ q ⊙ r) (⊙rev p) ⟩
                   refl _ ⊙ r
                 ＝⟨ refl⊙ r ⟩
                   r
                 ∎))

-- Anything equal to the identity map is quasi-invertible.
QInv-idmap : (A : Type) → QInv (idmap A)
QInv-idmap A = idmap A , refl (idmap A) , refl (idmap A)

QInv-cong-＝idmap : {A : Type} (f : A ⇒ A) (p : idmap A ＝ f) (a₀ a₁ : A) → QInv (refl f ∙ a₀ ∙ a₁)
QInv-cong-＝idmap f p a₀ a₁ = 𝐉 (λ f p → QInv (refl f ∙ a₀ ∙ a₁)) (QInv-idmap _) f p

-- The action on identifications of a quasi-invertible map is
-- quasi-invertible.  The slick proof of this using the 2-out-of-6
-- property hearkens back to the proof in classical algebraic topology
-- that a homotopy equivalence is a weak homotopy equivalence
-- (i.e. induces an isomorphism on all homotopy groups *with all
-- basepoints* -- the homotopy equivalence is not based).
QInv-＝ : {A B : Type} (f : A ⇒ B) (qf : QInv f) (a₀ a₁ : A) →
  QInv (refl f ∙ a₀ ∙ a₁)
QInv-＝ f qf a₀ a₁ =
  let g = fst qf
      sect = fst (snd qf)
      retr = snd (snd qf) in
  ∘QInv-2/6 (refl f ∙ a₀ ∙ a₁) (refl g ∙ (f ∙ a₀) ∙ (f ∙ a₁)) (refl f ∙ (g ∙ (f ∙ a₀)) ∙ (g ∙ (f ∙ a₁)))
    (QInv-cong-＝idmap (g ∘ f) (rev sect) a₀ a₁)
    (QInv-cong-＝idmap (f ∘ g) (rev retr) (f ∙ a₀) (f ∙ a₁))

-- Being a proposition transfers across quasi-inverses.
isProp-QInv : {A B : Type} → (A ≋ B) → isProp A → isProp B
isProp-QInv {A} {B} qi pA = ƛ b₀ ⇒ ƛ b₁ ⇒
  let f = fst qi
      g = fst (snd qi)
      sect = fst (snd (snd qi))
      retr = snd (snd (snd qi)) in
  (begin
    b₀
  ＝⟨ rev (happly retr b₀) ⟩
    f ∙ (g ∙ b₀)
  ＝⟨ cong f (pA ∙ (g ∙ b₀) ∙ (g ∙ b₁)) ⟩
    f ∙ (g ∙ b₁)
  ＝⟨ happly retr b₁  ⟩
    b₁
  ∎)

-- This is a crucial lemma: if f and g are quasi-inverses, then they
-- are "adjoint" with respect to identification types: (f a ＝ b) is
-- equivalent to (a ＝ g b).
QInv-＝-adjoint : {A B : Type} (f : A ⇒ B) (qf : QInv f) (a : A) (b : B) →
  (a ＝ fst qf ∙ b) ≋ (f ∙ a ＝ b)
QInv-＝-adjoint {A} {B} f qf a b =
  let g = fst qf
      sect = fst (snd qf)
      retr = snd (snd qf) in
  (ƛ p ⇒ cong f p ⊙ (happly retr b)) ,
  ∘QInv (refl f ∙ a ∙ (g ∙ b)) (QInv-＝ f (g , sect , retr) a (g ∙ b))
        (ƛ p ⇒ p ⊙ happly retr b) (⊙QInvR (f ∙ a) (happly retr b))

-- Σ-types are functorial on fiberwise quasi-inverses.
Σ-QInv : {A : Type} (B C : A → Type) (f : (x : A) → B x ⇒ C x) (e : (x : A) → QInv (f x)) →
  QInv {Σ A B} {Σ A C} (ƛ w ⇒ fst w , f (fst w) ∙ (snd w))
Σ-QInv {A} B C f e = (ƛ w ⇒ fst w , fst (e (fst w)) ∙ (snd w)) ,
  funext (ƛ w ⇒ refl (fst w) ,
    coe← (Id-REFL[]▸ (Λ _ ⇨ A) (Λ z ⇨ B (top z)) (fst w) (fst (e (fst w)) ∙ (f (fst w) ∙ snd w)) (snd w))
         (happly (fst (snd (e (fst w)))) (snd w))) ,
  funext (ƛ w ⇒ refl (fst w) ,
    coe← (Id-REFL[]▸ (Λ _ ⇨ A) (Λ z ⇨ C (top z)) (fst w) (f (fst w) ∙ (fst (e (fst w)) ∙ snd w)) (snd w))
         (happly (snd (snd (e (fst w)))) (snd w)))

Σ≋ : {A : Type} (B C : A → Type) (f : (x : A) → (B x ≋ C x)) →
  (Σ A B) ≋ (Σ A C)
Σ≋ {A} B C f = (ƛ w ⇒ fst w , fst (f (fst w)) ∙ (snd w)) , Σ-QInv B C (λ x → fst (f x)) (λ x → snd (f x))

-- Finally, we can prove that every quasi-invertible map yields a 1-1
-- correspondence.  The correspondence is (f a ＝ b), and it's easy to
-- prove that this is 1-1 on one side since it's a based path-space.
-- For the other side, we use the adjointness property above to
-- rewrite (f a ＝ b) as (a ＝ g b), where g is the quasi-inverse, and
-- apply based path contractibility again.
QInv→11 : {A B : Type} (f : A ⇒ B) (fe : QInv f) → 11Corr A B
QInv→11 {A} {B} f qf =
  let g = fst qf
      sect = fst (snd qf)
      retr = snd (snd qf) in
  (ƛ a ⇒ ƛ b ⇒ f ∙ a ＝ b) ,
  (ƛ a ⇒ (f ∙ a , refl (f ∙ a)) , isProp-sing→ (f ∙ a)) ,
  (ƛ b ⇒ (g ∙ b , retr ∙ b ∙ b ∙ refl b) ,
    isProp-QInv
      (Σ≋ (λ a → a ＝ g ∙ b) (λ a → f ∙ a ＝ b) (λ a → QInv-＝-adjoint f (g , sect , retr) a b))
      (isProp-sing← (g ∙ b)))
