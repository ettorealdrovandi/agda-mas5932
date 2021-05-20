---
title: "Joyal"
description: "Joyal's weak equivalences are the bi-invertible maps"
---

### Contents {#top}

1. [Joyal weak equivalences](#bi-inv)
1. [Joyal weak equivalences are isomorphisms](#eq-to-iso)
1. [Identity is a weak equivalence](#id-is-eq)
1. [Standard properties and reasoning](#eq-reason)

--------------------------------------------------


```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.equivalence.joyal where

open import mltt
open import function
open import hlevels
open import homotopy.retraction
open import homotopy.fibrations

open ≡-Reasoning
open ◾-lemmas
open ~-lemmas
```

### Joyal weak equivalences {#bi-inv}

`f : A → B` is a weak equivalence in the sense of Joyal if it is
*bi-invertible*, namely it has a left and a right inverse.

```agda
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where
  lfuninv : (A → B) → Set (ℓ ⊔ ℓ')
  lfuninv f = Σ[ h ∈ (codomain f → domain f) ] ( (h ∘′ f) ~ id)

  rfuninv : (A → B) → Set (ℓ ⊔ ℓ')
  rfuninv f = Σ[ g ∈ (codomain f → domain f) ]  ( (f ∘′ g) ~ id)

  iseq : (A → B) → Set (ℓ ⊔ ℓ')
  iseq f = rfuninv f × lfuninv f

  is-eq = iseq
  is-jeq = iseq
  isjeq = iseq

_≃j_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set _ --(ℓ ⊔ ℓ')
A ≃j B = Σ[ f ∈ (A → B) ] (iseq f)
```

### Joyal weak equivalences are isomorphisms {#eq-to-iso}

```agda
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where
  ≅→≃j : A ≅ B → A ≃j B
  ≅→≃j (hoeq f g ε η) = f , ((g , ε) , (g , η))

  ≃j→≅ : A ≃j B → A ≅ B
  _≅_.to (≃j→≅ (f , (g , ε) , h , η)) = f
  _≅_.from (≃j→≅ (f , (g , ε) , h , η)) = g
  _≅_.ε (≃j→≅ (f , (g , ε) , h , η)) = ε
  _≅_.η (≃j→≅ (f , (g , ε) , h , η)) = (δ ~∘ f) ~◾~ η
    where
      open ~-lemmas
      δ : g ~ h
      δ = ((η ~∘ g) ~⁻¹) ~◾~ ( h ∘~ ε )

  -- This is for compatibility with a previous version of this development
  iseq→qinv : (f : A → B) → iseq f → qinv f
  iseq→qinv f is = record { inv = from (≃j→≅ (f , is))
                          ; ε = ε (≃j→≅ (f , is))
                          ; η = η (≃j→≅ (f , is)) }
    where
      open _≅_
```

### Identity is a weak equivalence {#id-is-eq}

```agda
iseq-id : ∀ {ℓ} {A : Set ℓ} → iseq (𝓲𝓭 A)
iseq-id = (id , (λ _ → refl)) , (id , λ _ → refl)
```

### Standard properties and reasoning {#eq-reason}

The type `A ≃j B` satisfies the standard equivalence relation
properties. We use this to build a "Reasoning" module.

**Note:** Transitivity is superseded and subsumed by the
  "two-out-of-three" property, which is proved elsewhere in this
  development.

```agda
module ≃j-lemmas where

  open ≅-lemmas

  refl-≃j : ∀ {ℓ} {A : Set ℓ} → A ≃j A
  refl-≃j = id , iseq-id

  ≃j-sym : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃j B → B ≃j A
  ≃j-sym (f , is) = let φ = ≃j→≅ (f , is) 
                    in ≅→≃j (φ ≅⁻¹)

  ≃j-trans : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
             A ≃j B → B ≃j C → A ≃j C
  π₁ (≃j-trans (f , i) (g , j)) = g ∘′ f
  π₁ (π₂ (≃j-trans (f , i) (g , j))) = let r , ε = π₁ i
                                           v , τ = π₁ j
                                       in (r ∘′ v) , (( g ∘~ (ε ~∘ v)) ~◾~ τ)
  π₂ (π₂ (≃j-trans (f , i) (g , j))) = let l , η = π₂ i
                                           u , σ = π₂ j
                                       in (l ∘′ u) , ((l ∘~ (σ ~∘ f)) ~◾~ η)

  -- Syntax declarations
  ≃j-id = refl-≃j
  syntax ≃j-sym f = f ≃j⁻¹
  syntax ≃j-trans f g = f ≃◾≃j g
  -- ---------------------------

module ≃j-Reasoning where
  
  open ≃j-lemmas

  infix 3 _≃j∎
  infixr 2 _≃j⟨_⟩_
  infix 1 begin≃j_

  begin≃j_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
             A ≃j B → A ≃j B
  begin≃j p = p
  
  _≃j⟨_⟩_ : ∀ {ℓ ℓ' ℓ''} (A : Set ℓ) {B : Set ℓ'} {C : Set ℓ''} → A ≃j B → B ≃j C → A ≃j C
  A ≃j⟨ e ⟩ f = e ≃◾≃j f

  _≃j∎ : ∀ {ℓ} (A : Set ℓ) → A ≃j A
  A ≃j∎ = ≃j-id {A = A}
```


<!--
**FIXME** This should be elsewhere
-->

Equality is a weak equivalence. This is one direction (the easy one)
of the correspondence underlying the univalence principle.

```agda
transport-is-≃j : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A}
                  (p : x ≡ y) → is-eq (transport P p)
transport-is-≃j refl = iseq-id

≡→≃j : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃j B
≡→≃j p = (Id→Fun p) , (transport-is-≃j p)

≡→≃j' : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃j B
≡→≃j' refl = refl-≃j
  where
    open ≃j-lemmas
```

<p style="font-size: smaller; text-align: right">[top ⇑](#top)</p>
---
