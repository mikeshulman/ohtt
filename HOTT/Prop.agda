{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K --experimental-lossy-unification --no-import-sorts #-}

module HOTT.Prop where

open import HOTT.Rewrite using (Type; _≡_; _≡ᵉ_; coe→; coe←)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Square.Base
open import HOTT.Fill
open import HOTT.Pi.Base
open import HOTT.Sigma.Base
open import HOTT.Universe.Base
open import HOTT.Sum.Base
open import HOTT.Groupoids
open import HOTT.Univalence

infixr 30 fa exists

------------------------------
-- The type of propositions
------------------------------

Prop : Type
Prop = Σ[ P ⦂ Type ] isProp P

-- Equality of propositions is bi-implication
＝-isProp-iff : {P Q : Type} (pP : isProp P) (pQ : isProp Q) →
  (P ⇒ Q) → (Q ⇒ P) → (P ＝ Q)
＝-isProp-iff pP pQ f g = ua≋ (f , g , funext (ƛ x ⇒ pP ∙ _ ∙ _) , funext (ƛ y ⇒ pQ ∙ _ ∙ _))

isEquiv-props : {P Q : Type} (pP : isProp P) (pQ : isProp Q) (f : P ⇒ Q) →
  isEquiv f ＝ (Q ⇒ P)
isEquiv-props {P} {Q} pP pQ f = ＝-isProp-iff (isProp-isEquiv f) (isProp-Π (λ _ → pP))
  (ƛ ef ⇒ ƛ y ⇒ fst (fst (ef ∙ y)))
  (ƛ g ⇒ ƛ y ⇒ (g ∙ y , pQ ∙ _ ∙ _) , isProp-Σ pP λ x → isProp-＝ pQ (f ∙ x) y)

＝Prop : (P Q : Prop) → (P ＝ Q) ＝ ((fst P ⇒ fst Q) × (fst Q ⇒ fst P))
＝Prop P Q =
  begin
    P ＝ Q
  ＝⟨ ＝Σ-prop isProp isProp-isProp P Q ⟩
    fst P ＝ fst Q
  ＝⟨ ＝-coe≃ (fst P) (fst Q) ⟩
    fst P ≃ fst Q
  ＝⟨ cong (ƛ B ⇒ Σ (fst P ⇒ fst Q) (λ x → B ∙ x)) (funext (ƛ f ⇒ isEquiv-props (snd P) (snd Q) f)) ⟩
    (fst P ⇒ fst Q) × (fst Q ⇒ fst P)
  ∎

＝Prop-iff : {P Q : Prop} → (fst P ⇒ fst Q) → (fst Q ⇒ fst P) → (P ＝ Q)
＝Prop-iff {P} {Q} f g = coe⇐ (＝Prop P Q) ∙ (f , g)

coe⇒Prop : {P Q : Prop} → (P ＝ Q) → (fst P ⇒ fst Q)
coe⇒Prop e = coe⇒ (cong (ƛ x ⇒ fst x) e)

coe⇐Prop : {P Q : Prop} → (P ＝ Q) → (fst Q ⇒ fst P)
coe⇐Prop e = coe⇐ (cong (ƛ x ⇒ fst x) e)

-- Prop is a set
isSet-Prop : isSet Prop
isSet-Prop = ƛ P ⇒ ƛ Q ⇒ tr⇐ (ƛ X ⇒ isProp X) (＝Prop P Q) (isProp-× (isProp-Π (λ _ → snd Q)) (isProp-Π (λ _ → snd P)))

-- Identifications in a subtype
＝ΣProp : {A : Type} (B : A ⇒ Prop) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) {b₀ : fst (B ∙ a₀)} {b₁ : fst (B ∙ a₁)}
  → (a₀ , b₀) ＝ (a₁ , b₁)
＝ΣProp B p = p , Id-prop _ (λ a → fst (B ∙ a)) (λ a → snd (B ∙ a)) _ _

------------------------------
-- Propositional truncation
------------------------------

∥_∥ : Type → Type
∥ A ∥ = Π[ P ⦂ Type ] isProp P ⇒ (A ⇒ P) ⇒ P

∣_∣ : {A : Type} → A → ∥ A ∥
∣ a ∣ = ƛ P ⇒ ƛ _ ⇒ ƛ f ⇒ f ∙ a

isProp-∥∥ : (A : Type) → isProp ∥ A ∥
isProp-∥∥ A = isProp-Π (λ P → isProp-Π (λ prp → isProp-Π (λ _ → prp)))

∥∥-elim : {A : Type} (P : ∥ A ∥ → Type) (p : (x : ∥ A ∥) → isProp (P x))
  (d : (a : A) → P (∣ a ∣)) (u : ∥ A ∥) →
  P u
∥∥-elim {A} P p d u =
  coe⇒ (cong (ƛ x ⇒ P x) (isProp-∥∥ A ∙ _ ∙ u)) ∙
    (snd (u ∙ Σ _ P ∙ (ƛ x ⇒ ƛ y ⇒ ＝ΣProp (ƛ x ⇒ (P x , p x)) (isProp-∥∥ A ∙ fst x ∙ fst y) {snd x} {snd y}) ∙ (ƛ a ⇒ (∣ a ∣ , d a))))

∥∥-rec : {A : Type} (P : Prop) (d : A → fst P) → ∥ A ∥ → fst P
∥∥-rec {A} P d u = u ∙ fst P ∙ snd P ∙ (ƛ x ⇒ d x)

------------------------------
-- The logic of propositions
------------------------------

_∧_ : Prop → Prop → Prop
P ∧ Q = (fst P × fst Q , isProp-× (snd P) (snd Q))

_∨_ : Prop → Prop → Prop
P ∨ Q = (∥ fst P ⊎ fst Q ∥ , isProp-∥∥ _)

_⊃_ : Prop → Prop → Prop
P ⊃ Q = ((fst P ⇒ fst Q) , isProp-Π (λ _ → snd Q))

fa : (A : Type) (P : A → Prop) → Prop
fa A P = ((Π[ x ⦂ A ] fst (P x)) , isProp-Π (λ x → snd (P x)))

syntax fa A (λ x → P) = ∀[ x ⦂ A ] P

exists : (A : Type) (P : A → Prop) → Prop
exists A P = (∥ Σ[ x ⦂ A ] fst (P x) ∥ , isProp-∥∥ _)

syntax exists A (λ x → P) = ∃[ x ⦂ A ] P

∃-elim : {A : Type} (P : A → Prop) (Q : Prop) (d : (a : A) → fst (P a) → fst Q)
  (u : fst (∃[ x ⦂ A ] P x)) → fst Q
∃-elim P Q d u = ∥∥-rec Q (λ v → d (fst v) (snd v)) u
