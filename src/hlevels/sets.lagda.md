---
title: "h-Levels: Sets"
description: "Examples of known types that are  propositions or sets"
---


--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe --exact-split #-}

module hlevels.sets where

open import level
open import mltt
open import hlevels.core


open ≡-Reasoning
open ◾-lemmas
```

### The empty type

The empty type is a proposition (not completely trivial) and hence a set.

```agda
𝟘-is-prop : is-prop 𝟘
𝟘-is-prop = λ x y → !𝟘 y

𝟘-is-set : is-set 𝟘
𝟘-is-set = prop→set 𝟘-is-prop
```
We can give a direct proof of the latter:

```agda
𝟘-is-set' : is-set 𝟘
𝟘-is-set' = λ x y p q → !𝟘 y
```

### The unit type

```agda
𝟙-is-contr : is-contr 𝟙
𝟙-is-contr = * , (𝟙-induction (_≡_ *) refl)

𝟙-is-prop : is-prop 𝟙
𝟙-is-prop = singleton→prop 𝟙-is-contr

𝟙-is-set : is-set 𝟙
𝟙-is-set = prop→set 𝟙-is-prop
```
