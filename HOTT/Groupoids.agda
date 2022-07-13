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

-- We define contractible types to be inhabited propositions.
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

-- When proving something a proposition, we can assume it inhabited.
isProp-from-inhab : {A : Type} → (A → isProp A) → isProp A
isProp-from-inhab prpi = ƛ x ⇒ ƛ y ⇒ prpi x ∙ x ∙ y

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

-- We give the dependent version a different name, since it often requires specifying the type family.
funextd : {A : Type} (B : A → Type) {f g : Π A B} (p : Π[ x ⦂ A ] f ∙ x ＝ g ∙ x) → (f ＝ g)
funextd {A} B {f} {g} p = ƛ a₀ ⇒ ƛ a₁ ⇒ ƛ a₂ ⇒
  𝐉 (λ a₁ a₂ → Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) (f ∙ a₀) (g ∙ a₁)) (p ∙ a₀) a₁ a₂

-- It follows that propositions and contractible types are closed under Π.
isProp-Π : {A : Type} {B : A → Type} (pB : (x : A) → isProp (B x)) → isProp (Π A B)
isProp-Π pB = ƛ f ⇒ ƛ g ⇒ funextd _ (ƛ x ⇒ pB x ∙ (f ∙ x) ∙ (g ∙ x))

isContr-Π : {A : Type} {B : A → Type} (cB : (x : A) → isContr (B x)) → isContr (Π A B)
isContr-Π cB = ((ƛ x ⇒ fst (cB x)) , isProp-Π (λ x → snd (cB x)))

------------------------------
-- Retracts
------------------------------

-- A retract of a proposition or contractible type is again such.
isProp-retract : {A B : Type} (s : A ⇒ B) (r : B ⇒ A) (retr : r ∘ s ＝ idmap A) → isProp B → isProp A
isProp-retract s r retr prpB = ƛ a₀ ⇒ ƛ a₁ ⇒
  (begin
    a₀
  ＝⟨ rev (happly retr a₀) ⟩
    r ∙ (s ∙ a₀)
  ＝⟨ cong r (prpB ∙ (s ∙ a₀) ∙ (s ∙ a₁)) ⟩
    r ∙ (s ∙ a₁)
  ＝⟨ happly retr a₁ ⟩
    a₁
  ∎)

isContr-retract : {A B : Type} (s : A ⇒ B) (r : B ⇒ A) (retr : r ∘ s ＝ idmap A) → isContr B → isContr A
isContr-retract s r retr cB = (r ∙ fst cB , isProp-retract s r retr (snd cB))

Σ-retract : {A : Type} (B C : A → Type) (s : (x : A) → B x ⇒ C x) (r : (x : A) → C x ⇒ B x)
  (retr : (x : A) → r x ∘ s x ＝ idmap (B x)) →
  _∘_ {Σ A B} {Σ A C} {Σ A B}
    (ƛ u ⇒ (fst u , r (fst u) ∙ snd u)) (ƛ u ⇒ (fst u , s (fst u) ∙ snd u)) ＝ idmap (Σ A B)
Σ-retract {A} B C s r retr = funext (ƛ u ⇒ refl (fst u) ,
  coe← (Id-REFL[]▸ (Λ _ ⇨ A) (Λ w ⇨ B (top w)) (fst u) _ _) (happly (retr (fst u)) (snd u)))

------------------------------
-- isProp-isProp
------------------------------

-- Just as any two points in a proposition are identified, any two
-- points in a family of propositions are identified over anything in
-- the base.
Id-prop : {A : Type} {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (B : A → Type)
  (prp : (x : A) → isProp (B x)) (b₀ : B a₀) (b₁ : B a₁) →
  Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁
Id-prop {A} {a₀} {a₁} a₂ B prp b₀ b₁ =
   𝐉 (λ a₁ a₂ → (b₁ : B a₁) → Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁)
     (λ b₁' → prp a₀ ∙ b₀ ∙ b₁') a₁ a₂ b₁

-- A version of isProp-＝ for dependent identity types
isProp-Id : {A : Type} {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (B : A → Type)
  (prp : (x : A) → isProp (B x)) (b₀ : B a₀) (b₁ : B a₁) →
  isProp (Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁)
isProp-Id {A} {a₀} {a₁} a₂ B prp b₀ b₁ =
   𝐉 (λ a₁ a₂ → (b₁ : B a₁) → isProp (Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁))
     (λ b₁' → isProp-＝ (prp a₀) b₀ b₁') a₁ a₂ b₁

isContr-Id : {A : Type} {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (B : A → Type)
  (prp : (x : A) → isProp (B x)) (b₀ : B a₀) (b₁ : B a₁) →
  isContr (Id {ε▸ A} (Λ x ⇨ B (top x)) ([] ∷ a₀ ∷ a₁ ∷ a₂) b₀ b₁)
isContr-Id {A} {a₀} {a₁} a₂ B prp b₀ b₁ =
   (Id-prop a₂ B prp b₀ b₁ , isProp-Id a₂ B prp b₀ b₁)

-- Every square in a set can be filled.
sq-set : {A : Type} (prp : isSet A)
  {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
  (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
  Sq {ε} (Λ _ ⇨ A) [] a₀₂ a₁₂ a₂₀ a₂₁
sq-set {A} Aset {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  𝐉 (λ a₀₁ a₀₂ → (a₂₁ : a₀₁ ＝ a₁₁) → Sq (Λ⇨ (λ _ → A)) [] a₀₂ a₁₂ a₂₀ a₂₁)
    (λ a₂₁ → 𝐉 (λ a₁₁ a₁₂ → (a₂₁ : a₀₀ ＝ a₁₁) → Sq (Λ⇨ (λ _ → A)) [] (refl a₀₀) a₁₂ a₂₀ a₂₁)
      (λ a₂₁ → coe← (Id-REFL▸▸ {ε} (Λ _ ⇨ A) ((Λ _ ⇨ A) ⊚ ((Λ _ ⇨ᵉ []) ⊚ᵉ POP))
                               (Λ x ⇨ top (pop x) ＝ top x) [] a₀₀ a₁₀ a₂₀ a₂₁)
                    (Aset ∙ a₀₀ ∙ a₁₀ ∙ a₂₀ ∙ a₂₁) )
      a₁₁ a₁₂ a₂₁)
    a₀₁ a₀₂ a₂₁

-- A variation that uses a different kind of "square".  This is
-- actually morally the correct notion of square in a type dependent
-- on ε, but our definition of Sq comes out different because of the
-- non-reducing ⊚.
sq-set′ : {A : Type} (prp : isSet A)
  {a₀₀ a₀₁ : A} (a₀₂ : a₀₀ ＝ a₀₁) {a₁₀ a₁₁ : A} (a₁₂ : a₁₀ ＝ a₁₁)
  (a₂₀ : a₀₀ ＝ a₁₀) (a₂₁ : a₀₁ ＝ a₁₁) →
   Id {ε ▸ Λ⇨ (λ _ → A) ▸ Λ⇨ (λ _ → A)} (Λ z ⇨ top (pop z) ＝ top z)
       ([] ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁
sq-set′ {A} Aset {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁ =
  𝐉 (λ a₀₁ a₀₂ → (a₂₁ : a₀₁ ＝ a₁₁) → Id {ε ▸ Λ⇨ (λ _ → A) ▸ Λ⇨ (λ _ → A)} (Λ z ⇨ top (pop z) ＝ top z) ([] ∷ a₀₀ ∷ a₀₁ ∷ a₀₂ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁)
     (λ a₂₁ → 𝐉 (λ a₁₁ a₁₂ → (a₂₁ : a₀₀ ＝ a₁₁) → Id {ε ▸ Λ⇨ (λ _ → A) ▸ Λ⇨ (λ _ → A)} (Λ z ⇨ top (pop z) ＝ top z) ([] ∷ a₀₀ ∷ a₀₀ ∷ refl a₀₀ ∷ a₁₀ ∷ a₁₁ ∷ a₁₂) a₂₀ a₂₁)
      (λ a₂₁ → coe← (Id-REFL▸▸ {ε} (Λ _ ⇨ A) (Λ _ ⇨ A) (Λ x ⇨ top (pop x) ＝ top x) [] a₀₀ a₁₀ a₂₀ a₂₁)
                     (Aset ∙ a₀₀ ∙ a₁₀ ∙ a₂₀ ∙ a₂₁) )
      a₁₁ a₁₂ a₂₁)
    a₀₁ a₀₂ a₂₁

-- Being a proposition is a proposition
isProp-isProp : (A : Type) → isProp (isProp A)
isProp-isProp A = ƛ prp₀ ⇒ ƛ prp₁ ⇒
  ƛ a₀₀ ⇒ ƛ a₀₁ ⇒ ƛ a₀₂ ⇒ ƛ a₁₀ ⇒ ƛ a₁₁ ⇒ ƛ a₁₂ ⇒
  sq-set′ (isProp→isSet prp₀) a₀₂ a₁₂ (prp₀ ∙ a₀₀ ∙ a₁₀) (prp₁ ∙ a₀₁ ∙ a₁₁)

-- So is being contractible
isProp-isContr : (A : Type) → isProp (isContr A)
isProp-isContr A = isProp-from-inhab (λ prp → isProp-× (snd prp) (isProp-isProp A))

-- Any type satisfying axiom K is a set.
K→isSet : {A : Type} (k : (x : A) (p : x ＝ x) → refl x ＝ p) → isSet A
K→isSet k = ƛ x ⇒ ƛ y ⇒ ƛ p ⇒ ƛ q ⇒ 𝐉 (λ y p → (q : x ＝ y) → p ＝ q) (k x) y p q

------------------------------
-- 1-1 correspondences
------------------------------

is11 : {A B : Type} (R : A ⇒ B ⇒ Type) → Type
is11 {A} {B} R = Π A (λ a → isContr (Σ B (λ b → R ∙ a ∙ b))) × Π B (λ b → isContr (Σ A (λ a → R ∙ a ∙ b)))

11Corr : Type → Type → Type
11Corr A B = Σ (A ⇒ B ⇒ Type) is11
