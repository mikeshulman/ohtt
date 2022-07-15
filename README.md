# Higher Observational Type Theory

## Overview

This is an implementation in Agda of Higher Observational Type Theory (a.k.a. Observational Homotopy Type Theory, especially in case-insensitive contexts such as github repository names).

It is a "very shallow" embedding using Agda's experimental `--two-level` type theory: the fibrant fragment contains HOTT with its homotopical identity type, while the strict equality of the exo-fragment represents the definitional equality of HOTT.  In addition, we declare most of these definitional equalities to be rewrite rules using Agda's `--rewriting` feature, thereby making them into definitional equalities in Agda and therefore much more practical to use.  These rewrite rules are not globally confluent and potentially break subject reduction, but I believe that when restricted to the HOTT fragment they become so.

This is not a formalization *of* HOTT that can be used to prove metatheorems about it; it is intended as an experimental way to formalize results *in* HOTT.  Of necessity, when setting up the library we must engage with some metatheory, such as postulating the expected admissible equalities and coercing along them (when rewriting fails) to ensure that each rewrite rule is well-typed.  However, we intend to set things up so that when working in the HOTT fragment these coercions always vanish.

## Agda options

In addition to `--rewriting` and `--two-level`, we of course have to use the flag `--without-K` to have any consistent homotopical identity type.  (Note that when combined with `--two-level` this applies only to the fibrant fragment; axiom K is still provable for exo-types.)

We also currently use `--type-in-type` to avoid the bureaucracy of universe polymorphism.  Eventually, if the library becomes more widely used, we could migrate away from this.

We use `--exact-split` mainly on principle.

Finally, the flag `--experimental-lossy-unification` substantially speeds up typechecking of some files in the library.

## Installation

We depend on several bug-fixes and enhancements to Agda that have not made it into a released version yet (they are slated for 2.6.3), so you will need to compile the development version of Agda.

There is an `ohtt.agda-lib` file in the repository root, so you should be able to configure it as an Agda library in the usual way.  All files that load the library must use the `--rewriting` and `--two-level` options, of course, and `--without-K` should be given for consistency.

It should be sufficient to import `HOTT.Core` to get everything you need.  The file `HOTT.Everything` includes some extra stuff that's theoretically interesting but unneeded (like non-dependent function types and product types that are primitive rather than defined in terms of the dependent ones).

## Use

Once the library is complete, working in the HOTT fragment should hopefully be like ordinary (homotopical) Agda but with the added computing HOTT identity type.  The main difference is that we must restrict ourselves to the type and term formers whose HOTT behavior (computation laws for identity types and `ap`) has been defined in the library.

This means that we can't use pattern-matching, but must always define functions using eliminators.  This includes

- `fst` and `snd` for Σ-types.
- `case` for sum types.
- `ind` for the natural numbers.
- `ℤcase` for the integers.
- `𝟚-case` for the booleans.
- `⊥-elim` for the empty type.

It also means that instead of Agda's built-in function types `(x : A) → B x` we must use a wrapper around them denoted `Π[ x ﹕ A ] B x` (and `A ⇒ B` in the non-dependent case), with wrapped abstraction `ƛ x ⇒ f` and application `f ∙ a`.  This applies to the parameters of all definitions.  Thus, for instance, instead of

```agda
swap : (A B : Type) → A × B → B × A
swap (a , b) = (b , a)
```
we must write
```agda
swap : Π[ A ﹕ Type ] Π[ B ﹕ Type ] A × B ⇒ B × A
swap = ƛ A ⇒ ƛ B ⇒ ƛ u ⇒ (snd u , fst u)
```
Note that the colon inside the `Π[_]` is not the usual colon, which is not redefinable in Agda, but the unicode character SMALL COLON.  (The other characters used above are RIGHTWARDS DOUBLE ARROW, LATIN SMALL LETTER LAMBDA WITH STROKE, BULLET OPERATOR, and of course MULTIPLICATION SIGN.)  The SMALL COLON also appears in a similar notation for the sigma-type `Σ[ x ﹕ A ] B x`, which specializes to the non-dependent case as `A × B`.

In practice, we don't force ourselves to use the HOTT function-space exclusively, but only when defining functions that we expect to want to apply `refl` or `ap` to, or compare for equality.  This makes the notation a bit simpler.  But we really do have to avoid using Agda pattern-matching (including pattern-matching lambdas), as it breaks the rewrite rules that implement computation in HOTT.  This is unfortunate not only because it is inelegant and hard to read (we end up with long strings of `fst`s and `snd`s to access parts of a nested Σ-type), but because our definitions always get fully expanded out in the display of hole types, making goals harder to understand.  (As a partial remedy for this, rather than defining ℕ and ℤ as instances of their general classes of inductive types, we make them and their equality types separate special cases.)

The identity type of `x : A` and `y : A` is denoted `x ＝ y` with the unicode character FULLWIDTH EQUALS SIGN, since Agda reserves the ordinary equals sign `=` for definitions, while the commonly-used `≡` has undesired connotations of judgmental equality (or modular congruence).  Indeed, internal to the library we use `≡` for the strict exo-equality (and `≡ᵉ` for the exo-equality on exo-types), although ideally the user should not have to think about this.  The fullwidth equals sign is not available by default in Agda's Unicode input mode, but you can make it available (e.g. as `\=`) by customizing `agda-input-user-translations`.

The dependent identity type is written `Id B δ x y` and the (dependent) application to an identification is written `ap f δ`.  However, here `δ` is an identification in a *telescope*, and similarly `B` and `f` take a telescope as input.  Telescopes in the library are exotypes, but hopefully the user should be able to avoid working with telescopes by referring to reflexivities instead.  Namely, given `B : A ⇒ Type` (note it belongs to the wrapped function-type), the dependent identity type over `a₂ : a₀ ＝ a₁` is `fst ((refl B ∙ a₀ ∙ a₁ ∙ a₂) ↓)`.  Similarly, given `f : Π[ x ﹕ A ] B x`, its application to `a₂ : a₀ ＝ a₁` is `refl f ∙ a₀ ∙ a₁ ∙ a₂`.  We may define abbreviations for these.
