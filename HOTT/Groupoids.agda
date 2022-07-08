{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --experimental-lossy-unification #-}

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

infixr 35 _•_

------------------------------
-- Path operations
------------------------------

_•_ : {A : Type} {x y z : A} (p : x ＝ y) (q : y ＝ z) → x ＝ z
_•_ {A} {x} {y} {z} p q = comp→ {ε} (Λ _ ⇨ A) [] {x} {x} (refl x) {y} {z} q p

rev : {A : Type} {x y : A} (p : x ＝ y) → (y ＝ x)
rev {A} {x} {y} p = comp→ {ε} (Λ _ ⇨ A) [] {x} {y} p {x} {x} (refl x) (refl x)

cong : {A B : Type} (f : A ⇒ B) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) → (f ∙ a₀ ＝ f ∙ a₁)
cong f {a₀} {a₁} a₂ = refl f ∙ a₀ ∙ a₁ ∙ a₂

tr⇒ : {A : Type} (B : A ⇒ Type) {x y : A} (p : x ＝ y) (b : B ∙ x) → B ∙ y
tr⇒ {A} B {x} {y} p b = tr→ {ε▸ A} (Λ x ⇨ B ∙ top x) ([] ∷ x ∷ y ∷ p) b

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
begin_ {A} (x ＝⟨ p ⟩ q) = _•_ {A} p (begin q)

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
isProp-sing : {A : Type} (a : A) → isProp (Σ[ y ﹕ A ] a ＝ y)
isProp-sing {A} a = (ƛ x ⇒ ƛ y ⇒ utr→ (Λ _ ⇨ A) [] a (fst x) (fst y) (snd x) (snd y) ,
                               ulift→ (Λ _ ⇨ A) [] a (fst x) (fst y) (snd x) (snd y))

isContr-sing : {A : Type} (a : A) → isContr (Σ[ y ﹕ A ] a ＝ y)
isContr-sing {A} a = ((a , refl a) , isProp-sing a)


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

-- This implies that the identity types of a contractible type are contractible.
isContr-＝ : {A : Type} (cA : isContr A) (a b : A) → isContr (a ＝ b)
isContr-＝ {A} cA@(center , prp) a b =
  (prp ∙ a ∙ b , isProp-＝ prp a b)

------------------------------
-- Identity elimination
------------------------------

-- As in cubical type theory, the identity eliminator is defined by
-- transporting across contractibility of the based path-space.
𝐉 : {A : Type} {a : A} (P : (x : A) → (a ＝ x) → Type) (d : P a (refl a))
  (x : A) (e : a ＝ x) → P x e
𝐉 {A} {a} P d x e = tr⇒ (ƛ z ⇒ P (fst z) (snd z)) (isProp-sing a ∙ (a , refl a) ∙ (x , e)) d

-- In deducing the typal computation rule for 𝐉, the central lemma is
-- that transporting along anything equal to refl is the identity.
-- Note that it uses comp↑, which was defined using symmetry.
tr⇒＝refl : (A : Type) (B : A ⇒ Type) (a : A) (a₂ : a ＝ a) (a₂＝refl : a₂ ＝ refl a) (b : B ∙ a) →
  tr⇒ B a₂ b ＝ b
tr⇒＝refl A B a a₂ a₂＝refl b =
  comp↑ {ε▸ A} (Λ x ⇨ B ∙ top x)
        (sq∷ (Λ _ ⇨ A) [] {a} {a} (refl a) {a} {a} (refl a) a₂ (refl a)
              -- I don't understand why this doesn't fire as a rewrite here.
              (coe← (Id-REFL▸▸ (Λ _ ⇨ A) ((Λ⇨ (λ _ → A)) ⊚ ((Λ⇨ᵉ (λ _ → [])) ⊚ᵉ (Λ⇨ᵉ (pop {ε} {Λ⇨ (λ _ → A)}))))
                               (Λ⇨ (λ x → top (pop x) ＝ top x)) [] a a a₂ (refl a))
                    a₂＝refl))
   {b} {b} (refl b)
   {tr→ {ε▸ A} (Λ x ⇨ B ∙ top x) ([] ∷ a ∷ a ∷ a₂) b} {b}
   (lift→ {ε▸ A} (Λ x ⇨ B ∙ top x) ([] ∷ a ∷ a ∷ a₂) b) (refl b)

-- This proof is, again, just like in cubical type theory.
𝐉β : {A : Type} {a : A} (P : (x : A) → (a ＝ x) → Type) (d : P a (refl a)) →
  𝐉 P d a (refl a) ＝ d
𝐉β {A} {a} P d = tr⇒＝refl (Σ[ x ﹕ A ] a ＝ x) (ƛ z ⇒ P (fst z) (snd z)) (a , refl a) _
  (isProp-＝ (isProp-sing a) (a , refl a) (a , refl a) ∙
    (isProp-sing a ∙ (a , refl a) ∙ (a , refl a)) ∙ (refl (a , refl a)) ) d 

------------------------------
-- 1-1 correspondences
------------------------------

is11 : {A B : Type} (R : A ⇒ B ⇒ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⇒ B ⇒ Type) is11

----------------------------------------
-- Other kinds of equivalences
----------------------------------------

QInv : {A B : Type} (f : A ⇒ B) → Type
QInv {A} {B} f = Σ[ g ﹕ B ⇒ A ] (g ∘ f ＝ idmap A) × (f ∘ g ＝ idmap B)

BiInv : {A B : Type} (f : A ⇒ B) → Type
BiInv {A} {B} f = (Σ[ g ﹕ B ⇒ A ] g ∘ f ＝ idmap A) × (Σ[ h ﹕ B ⇒ A ] f ∘ h ＝ idmap B)

QInv→BiInv : {A B : Type} (f : A ⇒ B) → QInv f → BiInv f
QInv→BiInv f (g , sect , retr) = (g , sect) , (g , retr)

BiInv→QInv : {A B : Type} (f : A ⇒ B) → BiInv f → QInv f
BiInv→QInv {A} {B} f ((g , sect) , (h , retr)) = h ,
  (begin
     h ∘ f
   ＝⟨⟩
     idmap A ∘ h ∘ f
   ＝⟨ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ rev {A ⇒ A} {g ∘ f} sect ∙ (h ∙ (f ∙ a₀)) ∙ (h ∙ (f ∙ a₁)) ∙ (cong (h ∘ f) a₂)) ⟩
     g ∘ f ∘ h ∘ f
   ＝⟨ (ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒ cong g (retr ∙ (f ∙ a₀) ∙ (f ∙ a₁) ∙ (cong f a₂))) ⟩
     g ∘ idmap B ∘ f
   ＝⟨⟩
     g ∘ f
   ＝⟨ sect ⟩
     idmap A
   ∎) , retr
