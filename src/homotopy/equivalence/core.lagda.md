---
title: "Core Weak equivalences"
description: "Voevodsky's definition via contractible homotopy fibers"
---

### Contents {#top}

1. [Voevodsky's weak equivalences](#vweq)
1. [Weak equivalences are isomorphisms](#weq-to-iso)
1. [Identity is a weak equivalence](#idweq)
1. [Isomorphisms are weak equivalences](#iso-to-weq)

--------------------------------------------------


```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.equivalence.core where

open import mltt
open import function
open import hlevels
open import homotopy.retraction
open import homotopy.fibrations

open ≡-Reasoning
open ◾-lemmas
```

### Voevodsky's weak equivalences {#vweq}

Rationale: if `f : A → B` has contractible homotopy fibers, then
standard arguments in Topology imply that `A` and `B` have isomorphic
homotopy groups, which is the standard definition of weak equivalence.

```agda
isweq : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
isweq  f = Π[ b ∈ codomain f ] iscontr (hfib f b)

is-weq = isweq

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isweq f)
```

### Weak equivalences are isomorphisms {#weq-to-iso}

Convert weak equivalences to homotopy equivalences

```agda
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where
  weq-inverse : A ≃ B → (B → A)
  weq-inverse f b = let (_ , is) = f in hfib-pt ( center (is b) )

  -- better name
  invert = weq-inverse

  ≃→≅ : A ≃ B → A ≅ B
  ≃→≅ (f , is) = hoeq f g ε η
    where
      g : B → A
      g = λ b → hfib-pt (center (is b))
  
      ε : f ∘′ g ~ id
      ε = λ b → hfib-path (center (is b))
  
      η : g ∘′ f ~ id
      η a =  ap π₁ (δ (a , idp (f a)))
        where
          δ = centrality (is (f a))


  -- This is for compatibility with a previous version of this development

  weq→qinv : (f : A → B) → (isweq f) → (qinv f)
  weq→qinv f is = record { inv = from (≃→≅ (f , is)) ; ε = ε (≃→≅ (f , is)) ; η = η (≃→≅ (f , is)) }
    where open _≅_
```

### Identity is a weak equivalence {#idweq}

The identity map has contractible fibers, and hence is a weak equivalence

```agda
iscontr-hfib-id : ∀ {ℓ} {A : Set ℓ} (a : A) → iscontr (hfib id a)
π₁ (iscontr-hfib-id a) = a , (idp a)
π₂ (iscontr-hfib-id a) = λ { (a' , refl) → refl}

isweq-id : ∀ {ℓ} {A : Set ℓ} → isweq (𝓲𝓭 A)
isweq-id = iscontr-hfib-id
```

### Isomorphisms are weak equivalences {#iso-to-weq}

Consider  a retraction `r : B → A` such that the homotopy fiber of `s ∘ r
: B → B` at `b : B` is contractible. Then the homotopy fiber of `s : A
→ B` over `b : B` is also contractible.

```agda
Lemma1 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
         ((r , (s , η)) : Σ (B → A) (λ r → has-sect r)) (b : B) → 
         iscontr (hfib (s ∘′ r) b) → iscontr (hfib s b)
Lemma1  (r , (s , η)) b  =  singleton-retract t
    where
      t : (hfib s b) ◅ (hfib (s ∘′ r) b)
      t = Σ-pullback-retract r (s , η)

  -- UniMath names
iscontrhfiberandhretract = Lemma1
iscontr-hfib-retract = Lemma1
```

If there is a pointwise homotopy from `f : A → B` to `g : A → B` and
the homotopy fiber of `g` over `b : B` is contractible, then so is the
homotopy fiber of `f` over `b : B`

```agda
Lemma2 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
         {f g : A → B} (η : f ~ g) (b : B) →
         iscontr (hfib g b) → iscontr (hfib f b)
Lemma2 {f = f} {g} η b = singleton-retract ◅t
    where
      t : Σ[ ξ ∈ ((hfib g b) → (hfib f b)) ] (has-sect ξ)
      π₁ t (a , δ) = a , ((η a) ◾ δ)
      π₁ (π₂ t) (a , γ) = a , ((η a) ⁻¹ ◾ γ)
      π₂ (π₂ t) (a , γ) = PathPair→PathΣ {u = (π₁ t (π₁ (π₂ t) (a , γ)))} {v = (a , γ)} pp
        where
          pp : PathPair {P = λ a → (f a) ≡ b} (a , (η a ◾ (η a ⁻¹ ◾ γ))) (a , γ)
          π₁ pp = idp a
          π₂ pp = η a ◾ (η a ⁻¹ ◾ γ) ≡⟨ (assoc (η a) (η a ⁻¹) γ) ⁻¹ ⟩
                  (η a ◾ η a ⁻¹) ◾ γ ≡⟨ ap (_◾ γ) (rinv (η a)) ⟩
                  γ ∎
      ◅t : (hfib f b) ◅ (hfib g b)
      ◅t = from ◅-struct-iso t
        where open _≅_

  -- UniMath names
iscontrhfiberandhomot = Lemma2
iscontr-hfib-homot = Lemma2
```

If `f : A → B` is quasi-invertible, then we have data `g : B → A`, `ε
: f ∘ g ~ id`, and `η : g ∘ f ~ id`. We interpret `f` as the section
of a retraction `g` and then, for all `b : B`, use the chain

    iscontr (hfib id b) → iscontr (hfib (f ∘′ g) b) → iscontr (hfib f b)

where the first arrow is due to `Lemma2` and the second to
`Lemma1`. Therefore we have

```agda
≅→≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≅ B → A ≃ B
π₁ (≅→≃ (hoeq f g ε η)) = f
π₂ (≅→≃ (hoeq f g ε η)) b = first (second (iscontr-hfib-id b))
    where
      first : iscontr (hfib (f ∘′ g) b) → iscontr (hfib f b)
      first = Lemma1 (g , (f , η)) b

      second : iscontr (hfib id b) → iscontr (hfib (f ∘′ g) b)
      second = Lemma2  ε b
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---

<!--
**FIXME** This should be elsewhere
-->

```agda
module ≃-lemmas where

  refl≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
  refl≃ {ℓ} {A} = id , isweq-id
    where

  ≃-id = refl≃

  ≃-sym : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
  ≃-sym {A = A} {B} = ≅→≃ ∘′ ≅-sym ∘′ (≃→≅ {A = A} {B})
    where
      open ≅-lemmas
```

Equality is a weak equivalence. This is one direction (the easy one)
of the correspondence underlying the univalence principle.

```agda
transport-is-≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A}
                 (p : x ≡ y) → isweq (transport P p)
transport-is-≃ refl = isweq-id

≡→≃ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
≡→≃ p = Id→Fun p , transport-is-≃ p

≡→≃' : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
≡→≃' refl = ≃-id
  where
    open ≃-lemmas
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
