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
open import function.core
open import function.homotopyequivalence
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

Contractible types are isomorphic to `𝟙`, so we can prove the
"trivial" identity principle for `𝟙` from the HoTT book

```agda
iscontr-iso-𝟙 : ∀ {ℓ} {A : Set ℓ} → is-contr A → A ≅ 𝟙
iscontr-iso-𝟙 is = hoeq (λ _ → *)
                        (λ _ → center is)
                        (λ { * → refl})
                        (centrality is)

Id𝟙-is-𝟙 : {x y : 𝟙} → (x ≡ y) ≅ 𝟙
Id𝟙-is-𝟙 {x} {y} = iscontr-iso-𝟙 (is x y)
  where
    is : 𝟙 isofhlevel 1
    is = prop→hlevel1 𝟙-is-prop


Id𝟙-is-𝟙' : {x y : 𝟙} → (x ≡ y) ≅ 𝟙
Id𝟙-is-𝟙' = record { to = λ _ → *
                   ; from = λ _ → refl
                   ; ε = λ { * → refl}
                   ; η = λ { refl → refl}}
```
