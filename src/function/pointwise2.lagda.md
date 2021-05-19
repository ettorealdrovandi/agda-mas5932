---
title: "Function: pointwise2"
description: "Pointwise equality of pointwise equality"
---

```agda
{-# OPTIONS --without-K --safe #-}

module function.pointwise2 where

open import level
open import function.core
open import function.pointwise
open import mltt.identity.core
open import mltt.pi
```

For two dependent functions `f g : (x : A) → P x` and two homotopies,
i.e. pointwise equalities, `ε` and `η` between them, we define the
type of identifications `(x : A) → (ε x) ≡ (η x)`.

This corresponds to the idea of *homotopies of homotopies.*

```agda
infix 3 _≈_
_≈_ : ∀ {ℓ ℓ'} {A : Set ℓ}{P : A → Set ℓ'} 
      {f g : Π[ x ∈ A ] P x} (ε η : f ~ g) → Set (ℓ ⊔ ℓ')
_≈_ {A = A} ε η = Π[ x ∈ A ] (ε x ≡ η x)
```
