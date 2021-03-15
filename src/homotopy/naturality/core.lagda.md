---
title: "Naturality"
description: "Naturality constructions: core definitions"
---

There are two ideas:

1. Dependent functions can be seen as ∞-presheaves. Therefore given two such dependent functions, there is a space Hom of pointwise functions between them which we interpret as natural transformations, i.e. morphisms of presheaves. 

1. As expounded in the HoTT book, functions between types behave as functors with respect to paths, via the applicative `ap`. Then *homotopies* between functions behave as natural transformations.

   Recall that *homotopy* in this case means pointwise equality of (dependent) functions.

```agda
{-# OPTIONS --without-K --safe #-}

module homotopy.naturality.core where

open import level
open import function.core
open import function.pointwise
open import mltt.identity.core
open import mltt.identity.ap
open import mltt.identity.path-composition
open import mltt.sigma
open import mltt.pi
open import homotopy.twocatconstructions

open ◾-lemmas
```

[MHE](https://www.cs.bham.ac.uk/~mhe/TypeTopology/index.html), uses `Nat`. `Hom` is used elsewhere in these notes.

```agda
Nat : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} → (A → Set ℓ') → (A → Set ℓ'') → Set (ℓ ⊔ ℓ' ⊔ ℓ'')
Nat P Q = (x : domain P) → P x → Q x

Nat-natural : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} 
              (P : A → Set ℓ') (Q : A → Set ℓ'') (θ : Nat P Q)
              {x y : A} (p : x ≡ y) →
              θ y ∘′ transport P p ≡ transport Q p ∘′ θ x
Nat-natural P Q θ {x} {.x} refl = idp (θ x)

-- Nat-2natural here: find the correct statement

Nat→Σ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : A → Set ℓ''} →       
        Nat P Q → Σ A P → Σ A Q
Nat→Σ θ = λ { (a , u) → a , (θ a u)}

Nat→Π : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : A → Set ℓ''} →
        Nat P Q → Π A P → Π A Q
Nat→Π θ f = λ a → θ a (f a)
```

```agda
homot-natural : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} (h : f ~ g) {x y : A} (p : x ≡ y) →
                (h x) ◾ (ap g p) ≡ (ap f p) ◾ (h y)
homot-natural h {x} {.x} refl = ru  (h x)

homot-natural' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} (h : f ~ g) {x y : A} (p : x ≡ y) →
                 (ap f p) ◾ (h y) ≡ (h x) ◾ (ap g p)
homot-natural' h {x} {.x} refl = (ru (h x)) ⁻¹

-- dependent version
homot-natural-d : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {f g : Π A P} (h : f ~ g) {x y : A} (p : x ≡ y) →
                  ap (transport P p) (h x) ◾ (apd g p) ≡ (apd f p) ◾ (h y)
homot-natural-d h {x} {.x} refl = ap id (h x) ◾ refl ≡⟨ ru (ap id (h x)) ⟩
                                  ap id (h x) ≡⟨ apid (h x) ⟩
                                  h x ∎
  where
    open ap-lemmas
    open ≡-Reasoning
homNatD = homot-natural-d

homot-2natural : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} (h : f ~ g) 
                 {x y : A} {p q : x ≡ y} (α : p ≡ q) →
                 (homot-natural' h p) ◾ ((h x) ◾ˡ (ap2 g α)) 
                                 ≡ ((ap2 f α) ◾ʳ (h y)) ◾ (homot-natural' h q)
homot-2natural h {p = p} {.p} refl = ru (homot-natural' h p)
```
