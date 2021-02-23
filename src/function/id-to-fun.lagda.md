---
title: "Id-to-Fun"
description: "Id-to-Fun turns a proof of indentity into a function"
---

--------------------------------------------------

The function `Id→Fun : A ≡ B → (A → B)` is needed to prove simple
lemmas for decidable equality in simple types, such as 𝟚 or ℕ.

In fact, `Id→Fun p` is a weak equivalence, and the univalence
principle states that `Id→Fun` is itself a weak equivalence between `A
≡ B` and the type `A ≃ B` of weak equivalences between `A` and `B`,
however defined.

This will be taken up elsewhere.

--------------------------------------------------

```agda
{-# OPTIONS --without-K --safe #-}

module function.id-to-fun where

open import level
open import function.core
open import mltt.identity.core

Id→Fun : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
Id→Fun {ℓ} = transport (𝓲𝓭 (Set ℓ))

Id→Fun' : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
Id→Fun' {ℓ} {A} {.A} refl = 𝓲𝓭 A

Id→Funs-agree : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) → Id→Fun p ≡ Id→Fun' p
Id→Funs-agree {ℓ} {A} {.A} refl = idp (𝓲𝓭 A)
```
