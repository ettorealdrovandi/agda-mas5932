---
title: "h-Levels: Hedberg's Theorem"
description: "A proof of Hedberg's theorem"
---

### Contents {#top}

1. [Preliminary definitions](#prelims)
1. [Hedberg's theorem](#hedberg)
1. [Examples](#examples)

--------------------------------------------------

Hedberg's theorem states that if a type has decidable equality then it is a set. There are other equivalent formulations (see the [HoTT book][HoTT]), but this one contains a useful *criterion* to determine when a type is a set.  For this particular proof and related definitions we follow the paper [Generalization of Hedberg's Theorem][KECA] ([published version][KECA-pub]).

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module hlevels.hedberg where

open import level
open import mltt
open import logic.decidable
open import hlevels.core
open import hlevels.sets
open import hlevels.closure

open ≡-Reasoning
open ◾-lemmas
```

### Preliminary definitions {#prelims}

A type is *decidable* if `A + ¬ A`. Following our reference, we re-christen a type *discrete* it has a decidable equality:

```agda
discrete : ∀ {ℓ} → Set ℓ → Set ℓ
discrete A = decidable-equality A
```

A function is (weakly or homotopically) *constant* if its values are propositionally equal:
```agda
const : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set (ℓ ⊔ ℓ')
const f = (x y : domain f) → f x ≡ f y
```
and we say that a type is *collapsible* if there exists a constant endomorphism:
```agda
--collapsible
coll : ∀ {ℓ} → Set ℓ → Set ℓ
coll A = Σ[ f ∈ (A → A) ] const f
```

A decidable type is collapsible:
```agda
decidable→collapsible : ∀ {ℓ} {A : Set ℓ} → decidable A → coll A
decidable→collapsible {ℓ} {A} (inl a) = (λ x → a) , λ x y → refl
decidable→collapsible {ℓ} {A} (inr ¬a) = (λ x → !𝟘 (¬a x)) , (λ x y → ap !𝟘 (γ x y))
  where
    γ : (x y : A) → ¬a x ≡ ¬a y
    γ x y = 𝟘-is-prop (¬a x) (¬a y)
```
The technique of the proof is to observe that if `A` is true, namely we get `a : A`, then we can define a constant function `f : A → A` by simply assigning `λ x → a`, and therefore `refl` is a proof of constancy; if, on the other hand, we have `¬ A`, i.e. we have a term `¬a : A → 𝟘`, then for any `x : A` we get `¬a x : 𝟘`, and hence we get back to `A` using the (unique) map `!𝟘 : 𝟘 → A`. Then the proof of constancy uses that 𝟘 is a proposition to prove `¬a x ≡ ¬a y`, for all `x y : A`.


Finally, a type is *path-collapsible* if all its identity types are collapsible:

```agda
--path-collapsible
path-coll : ∀ {ℓ} → Set ℓ → Set ℓ
path-coll A = (x y : A) → coll (x ≡ y)
```

### Hedberg's theorem {#hedberg}

Discrete types are path-collapsible:

```agda
discrete→path-collapsible : ∀ {ℓ} {A : Set ℓ} → discrete A → path-coll A
discrete→path-collapsible d = λ x y → decidable→collapsible (d x y)

Lemma-1[Hedberg] = discrete→path-collapsible
```

Sets are path collapsible: the constant endo-function we need on each identity type is actually the identity, and the proof that the type is a set provides the proof of constancy for the endo-function:

```agda
--sets are path-collapsible
is-set→path-collapsible : ∀ {ℓ} {A : Set ℓ} → is-set A → path-coll A
is-set→path-collapsible {ℓ} {A} is x y = id , (λ p q → is x y p q)
```

The following lemma is very useful in its own right. It gives a more practical criterion to determine that a type is a set, by providing a constant endo-function on its identity types. The proof relies on the following non-obvious fact: assuming we are given for each `x y : A` an `f : x ≡ y → x ≡ y`, then we have that for each `r : x ≡ y`

    r ≡ (f x x refl) ⁻¹ ◾ (f x y r)

which is proved by path induction on `r`. Indeed, assuming `r = refl`, which means `y = x` the above reduces to

    refl ≡ (f x x refl) ⁻¹ ◾ (f x x refl)

which has an obvious proof. In its complete form, the lemma is:

```agda
--path-collapsible are sets
path-collapsible→is-set : ∀ {ℓ} {A : Set ℓ} → path-coll A → is-set A
path-collapsible→is-set {ℓ} {A} pc x y p q = lemma-3
  where
    f : (x y : A) → x ≡ y → x ≡ y
    f x y = π₁ (pc x y)

    f-is-const : (x y : A) (p q : x ≡ y) → f x y p ≡ f x y q
    f-is-const x y = π₂ (pc x y)

    lemma-1 : (x y : A) (r : x ≡ y) → r ≡ (f x x refl) ⁻¹ ◾ (f x y r)
    lemma-1 x .x refl = ( (linv (f x x refl)) ) ⁻¹

    lemma-2 : (f x x refl) ⁻¹ ◾ (f x y p) ≡ (f x x refl) ⁻¹ ◾ (f x y q)
    lemma-2 = ap (λ h → (f x x refl) ⁻¹ ◾ h) (f-is-const x y p q) 

    lemma-3 : p ≡ q
    lemma-3 = p                           ≡⟨ lemma-1 x y p ⟩
              (f x x refl) ⁻¹ ◾ (f x y p) ≡⟨ lemma-2 ⟩
              (f x x refl) ⁻¹ ◾ (f x y q) ≡⟨ (lemma-1 x y q) ⁻¹ ⟩
              q ∎

Lemma-2[Hedberg] = path-collapsible→is-set
```

And finally Hedberg's theorem:

```agda
--Hedberg's theorem
discrete→is-set : ∀ {ℓ} {A : Set ℓ} → discrete A → is-set A
discrete→is-set d = path-collapsible→is-set (discrete→path-collapsible d)

Thm[Hedberg] = discrete→is-set
```

### Examples {#examples}

```agda
module ℕ-is-set where
  
  open import types.naturals

  ℕ-is-discrete : discrete ℕ
  ℕ-is-discrete = ℕ-decidable-equality

  ℕ-is-set : isSet ℕ
  ℕ-is-set = discrete→is-set (ℕ-is-discrete)
```


<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

[HoTT]: https://homotopytypetheory.org/book
[MHE]: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
[KECA]: https://www.cs.bham.ac.uk/~mhe/papers/hedberg.pdf
[KECA-pub]: https://doi.org/10.1007/978-3-642-38946-7_14
[K]: http://www2.mathematik.tu-darmstadt.de/~streicher/HabilStreicher.pdf

