---
title: "Homotopy: star"
description: "Stars of points. The sigma types of paths emanating from a point"
---

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module homotopy.star where

open import level
open import mltt
open import hlevels.core
```

In Topology the *star* of a point is the space of paths emanating from (or ending to) that point; alternatively, it is the set of cells in a simplicial complex that it is incident to that point.

```agda
star : ∀ {ℓ} {A : Set ℓ} → A → Set ℓ
star {ℓ} {A} a = Σ[ x ∈ A ] (a ≡ x)

star' : ∀ {ℓ} {A : Set ℓ} → A → Set ℓ
star' {ℓ} {A} a = Σ[ x ∈ A ] (x ≡ a)
```

Small utilities:

```agda
star-center : ∀ {ℓ} {A : Set ℓ} (a : A) → star a
star-center a = a , (idp a)

star'-center : ∀ {ℓ} {A : Set ℓ} (a : A) → star' a
star'-center a = a , (idp a)

star-path-center : ∀ {ℓ} {A : Set ℓ} (a : A) (u : star a) → u ≡ (star-center a)
star-path-center a (.a , refl) = idp (a , refl)

star'-path-center : ∀ {ℓ} {A : Set ℓ} (a : A) (u : star' a) → u ≡ (star'-center a)
star'-path-center a (.a , refl) = idp (a , refl)

star-contr : ∀ {ℓ} {A : Set ℓ} (a : A) → is-singleton (star a)
star-contr a = (star-center a) , (λ u → (star-path-center a u) ⁻¹)

star'-contr : ∀ {ℓ} {A : Set ℓ} (a : A) → is-singleton (star' a)
star'-contr a = (star'-center a) , (λ u → (star'-path-center a u) ⁻¹)
```
