{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Bool where

open import HOTT.Rewrite using (Type; _≡_)
open import HOTT.Telescope
open import HOTT.Id
open import HOTT.Refl
open import HOTT.Transport
open import HOTT.Indices
open import HOTT.Sigma.Base
open import HOTT.Pi.Base
open import HOTT.Indices
open import HOTT.Groupoids

infix 35 _＝𝟚_

------------------------------
-- Generalized booleans
------------------------------

data bool (Ω : Type) (f t : Ω) : Ω → Type where
  false : bool Ω f t f
  true : bool Ω f t t

bool-case : {Ω : Type} {f t : Ω} (P : (x : Ω) → bool Ω f t x → Type)
  (then : P t true) (else : P f false)
  {ω : Ω} (b : bool Ω f t ω) → P ω b
bool-case P then else false = else
bool-case P then else true = then

------------------------------
-- Ordinary booleans
------------------------------

data 𝟚 : Type where
  false : 𝟚
  true : 𝟚

𝟚-case : (P : 𝟚 → Type) (then : P true) (else : P false) (b : 𝟚) → P b
𝟚-case P then else false = else
𝟚-case P then else true = then

----------------------------------------
-- Equality of ordinary booleans
----------------------------------------

data _＝𝟚_ : 𝟚 → 𝟚 → Type where
  false : false ＝𝟚 false
  true : true ＝𝟚 true

＝𝟚-case : (P : (u v : 𝟚) → (u ＝𝟚 v) → Type) (then : P true true true) (else : P false false false)
  {u v : 𝟚} (b : u ＝𝟚 v) → P u v b
＝𝟚-case P then else false = else
＝𝟚-case P then else true = then

------------------------------
-- Special path operations
------------------------------

refl𝟚 : (n : 𝟚) → (n ＝ n)
refl𝟚 n = refl n

rev𝟚 : {m n : 𝟚} → (m ＝ n) → (n ＝ m)
rev𝟚 p = rev {𝟚} p

_•𝟚_ : {x y z : 𝟚} → (x ＝ y) → (y ＝ z) → x ＝ z
p •𝟚 q = _•_ {𝟚} p q

refl＝𝟚 : {m n : 𝟚} (p : m ＝ n) → (p ＝ p)
refl＝𝟚 p = refl p

rev＝𝟚 : {m n : 𝟚} {p q : m ＝ n} → (p ＝ q) → (q ＝ p)
rev＝𝟚 {m} {n} r = rev {m ＝ n} r

_•＝𝟚_ : {m n : 𝟚} {x y z : m ＝ n} → (x ＝ y) → (y ＝ z) → x ＝ z
_•＝𝟚_ {m} {n} p q = _•_ {m ＝ n} p q

------------------------------
-- Identity types
------------------------------

postulate
  ＝-bool : (Ω : Type) (f t : Ω) (ω : Ω) (u v : bool Ω f t ω) →
    (u ＝ v) ≡
    bool (＝Idx Ω (bool Ω f t))
      (f , f , refl f , false , false) (t , t , refl t , true , true)
      (ω , ω , refl ω , u , v)
  Id-bool : {Δ : Tel} (Ω : el Δ → Type) (f t : (x : el Δ) → Ω x)
    (ω : (x : el Δ) → Ω x) (δ : el (ID Δ))
    (u₀ : bool (Ω (δ ₀)) (f (δ ₀)) (t (δ ₀)) (ω (δ ₀)))
    (u₁ : bool (Ω (δ ₁)) (f (δ ₁)) (t (δ ₁)) (ω (δ ₁))) →
    Id (Λ x ⇨ bool (Ω x) (f x) (t x) (ω x)) δ u₀ u₁ ≡
    bool (Id-Idx δ Ω (λ x y → bool (Ω x) (f x) (t x) y))
      (f (δ ₀) , f (δ ₁) , ap (Λ⇨ Ω) f δ , false , false )
      (t (δ ₀) , t (δ ₁) , ap (Λ⇨ Ω) t δ , true , true)
      (ω (δ ₀) , ω (δ ₁) , ap (Λ⇨ Ω) ω δ , u₀ , u₁)
  ＝-𝟚 : (u v : 𝟚) → (u ＝ v) ≡ (u ＝𝟚 v)

{-# REWRITE ＝-bool Id-bool ＝-𝟚 #-}

postulate
  ＝-＝𝟚 : (n₀ n₁ : 𝟚) (e₀ e₁ : n₀ ＝𝟚 n₁) →
    (e₀ ＝ e₁) ≡
    bool (Σ[ x₀ ⦂ 𝟚 ] Σ[ x₁ ⦂ 𝟚 ] (x₀ ＝ x₁) × (x₀ ＝ x₁))
      (false , false , false , false)
      (true , true , true , true)
      (n₀ , n₁ , e₀ , e₁)
  Id-＝𝟚 : {Δ : Tel} (δ : el (ID Δ)) (n₀ n₁ : el Δ → 𝟚)
    (e₀ : n₀ (δ ₀) ＝𝟚 n₁ (δ ₀)) (e₁ : n₀ (δ ₁) ＝𝟚 n₁ (δ ₁)) →
    Id {Δ} (Λ x ⇨ n₀ x ＝𝟚 n₁ x) δ e₀ e₁ ≡
    bool (Σ[ x₀₀ ⦂ 𝟚 ] Σ[ x₀₁ ⦂ 𝟚 ] Σ[ x₀₂ ⦂ x₀₀ ＝ x₀₁ ]
          Σ[ x₁₀ ⦂ 𝟚 ] Σ[ x₁₁ ⦂ 𝟚 ] Σ[ x₁₂ ⦂ x₁₀ ＝ x₁₁ ]
          (x₀₀ ＝𝟚 x₁₀) × (x₀₁ ＝𝟚 x₁₁))
      (false , false , false , false , false , false , false , false)
      (true , true , true , true , true , true , true , true)
      (n₀ (δ ₀) , n₀ (δ ₁) , ap (Λ _ ⇨ 𝟚) n₀ δ ,
       n₁ (δ ₀) , n₁ (δ ₁) , ap (Λ _ ⇨ 𝟚) n₁ δ ,
       e₀ , e₁)

{-# REWRITE ＝-＝𝟚 Id-＝𝟚 #-}

------------------------------
-- Negation
------------------------------

¬ : 𝟚 ⇒ 𝟚
¬ = ƛ x ⇒ 𝟚-case (λ _ → 𝟚) false true x

¬¬ : ¬ ∘ ¬ ＝ idmap 𝟚
¬¬ = funext {f = ¬ ∘ ¬} {g = idmap 𝟚}
  (ƛ x ⇒ 𝟚-case (λ x → ¬ ∙ (¬ ∙ x) ＝ x) true false x)

QInv-¬ : QInv ¬
QInv-¬ = ¬ , ¬¬ , ¬¬

11-¬ : 11Corr 𝟚 𝟚
11-¬ = QInv→11 ¬ QInv-¬
