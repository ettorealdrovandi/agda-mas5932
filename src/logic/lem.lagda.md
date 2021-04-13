---
title: "Excluded Middle"
description: "Small facts about the excluded middle"
---

```agda
{-# OPTIONS --without-K --safe #-}

module logic.lem where

open import level
open import mltt
open import logic.negation
open import hlevels.core
```

There is a statement that *can* be proved in the context of Martin-Löf Type Theory without assuming axioms: that the Excluded Middle is "irrefutable," namely that its double negation always holds.

In the following, recall that for any type, `¬ A = A → 𝟘`. In the proof we start with evidence `ξ : ¬ (A + ¬ A)` that is, `ξ : (A + ¬ A) → 𝟘`.

```agda
EM-is-irrefutable : ∀ {ℓ} (A : Set ℓ) → ¬¬ (A ⊎ ¬ A)
EM-is-irrefutable A ξ =  ξ  --takes a term of A + ¬ A
                         (inr --we choose ¬ A, since there's no A. But ¬ A = A → 𝟘
                           λ x → ξ ( inl x)) --x : A so to produce 𝟘 we apply ξ to its left injection

```

The "wild" Law of the Excluded Middle simply asserts that we can peel those two negation operators off. This *cannot* be proved, but we can write its type:

```agda
wLEM : ∀ ℓ → Set (lsuc ℓ)
wLEM ℓ = (A : Set ℓ) → A ⊎ ¬ A
```

We state its converse, that is, peeling off one negation operator from triple negation, as an axiom and we can write its type:


```agda
wLDN : ∀ ℓ → Set (lsuc ℓ)
wLDN ℓ = (A : Set ℓ) → (¬¬ A → A)
```

The two axioms *are* logically equivalent:

```agda
ldn-implies-lem : ∀ {ℓ} → wLDN ℓ → wLEM ℓ
ldn-implies-lem {ℓ} ldn A = ldn (A ⊎ ¬ A) dn-em
  where
    dn-em = EM-is-irrefutable A

lem-implies-ldn : ∀ {ℓ} → wLEM ℓ → wLDN ℓ
lem-implies-ldn lem A ¬¬a with (lem A)
lem-implies-ldn lem A ¬¬a | inl x = x
lem-implies-ldn lem A ¬¬a | inr x = !𝟘 (¬¬a x)

lem-implies-ldn' : ∀ {ℓ} → wLEM ℓ → wLDN ℓ
lem-implies-ldn' lem A = help (lem A)
  where
    help : (A ⊎ ¬ A) → (¬¬ A → A)
    help (inl a)  = λ _ → a
    help (inr ¬a) = λ ¬¬a → !𝟘 {B = A} (¬¬a ¬a)
```

<span style="color: teal; font-weight: bold">Remark</span> It is important to note the form of the two lemmas for the logical equivalence of LEM and LDN. For example, LEM → LDN is *not* formulated as

    (A : Set ℓ) → ( (A + ¬ A) → (¬¬ A → A))

as one might expect, but as:

     ((A : Set ℓ) →  (A + ¬ A)) → (B : Set ℓ) → (¬¬ B → B)

The difference is crucial: in order to prove LDN for a *given type $B$*, we need to know that LEM holds *for all* types.

A more reasonable version of the axiom is the following:

```agda
LEM : ∀ ℓ → Set (lsuc ℓ)
LEM ℓ = (A : Set ℓ ) → is-prop A → (A ⊎ ¬ A)
```
and

```agda
LDN : ∀ ℓ → Set (lsuc ℓ)
LDN ℓ = (A : Set ℓ) → is-prop A → (¬¬ A → A)
```

For mere propositions there is a compelling alternative characterization worked out in [MHE][MHE].

```agda
LEM' : ∀ ℓ → Set (lsuc ℓ)
LEM' ℓ = (A : Set ℓ) → is-prop A → (is-singleton A ⊎ is-empty A)
```

This says that if a type is a (mere) proposition, then it either is contractible or it is empty. The two versions are logically equivalent:

```agda
LEM-implies-LEM' : ∀ {ℓ} → LEM ℓ → LEM' ℓ
LEM-implies-LEM' lem A is with (lem A is)
LEM-implies-LEM' lem A is | inl  a = inl (inhabited-prop→singleton a is)
LEM-implies-LEM' lem A is | inr ¬a = inr ¬a

LEM'-implies-LEM : ∀ {ℓ} → LEM' ℓ → LEM ℓ
LEM'-implies-LEM lem' A is with (lem' A is)
... | inl issingl = inl (center {A = A} issingl)
... | inr ¬a      = inr ¬a
```

According to `LEM'`, a mere Proposition is either a singleton or it is empty. Without assuming it we can stil prove that *it is not the case* that there are mere proposition that are not singletons and also not empty. These are aptly called "unicorns" in [MHE][MHE]:

```agda
there-are-no-unicorns : ∀ {ℓ} →  ¬ ( Σ[ A ∈ Set ℓ ]  ((isProp A) × ( (¬ (isSingleton A)) × (¬ (is-empty A)))  ) )
there-are-no-unicorns (A , isp , f , g) = nothing
  where
    ¬a : is-empty A
    ¬a = λ x → f (inhabited-prop→singleton x isp)

    nothing : 𝟘
    nothing = g ¬a
```

We have actually *proved* the above statement, so we can exclude these "unicorns" exist. Therefore, if LEM is not assumed, it is the case that the possible propositions are the contractible types and the empty one, however there is no way in our type theory to determine which of the two alternatives occurs for a given (mere) proposition `A`.



<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

