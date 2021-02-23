---
title: "The type with two elements"
subtitle: "Standard and simple types in Martin-Löf Type Theory"
description: "Disjoint union (sum) of two unit types: the type with two canonical terms: 𝟚 is decidable"
---


```agda
{-# OPTIONS --without-K --safe #-}

module types.two.decidable where

open import level
open import mltt.sum
open import mltt.unit
open import mltt.empty
open import mltt.identity.core
open import types.two.core
open import logic.negation
open import logic.decidable
```

```agda
₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ = ≢-inv (inl-is-not-inr {A = 𝟙} {B = 𝟙} {*} {*})
```

```agda
𝟚-decidable-equality : decidable-equality 𝟚
𝟚-decidable-equality ₀ ₀ = inl (idp ₀)
𝟚-decidable-equality ₀ ₁ = inr (≢-inv ₁-is-not-₀)
𝟚-decidable-equality ₁ ₀ = inr (₁-is-not-₀)
𝟚-decidable-equality ₁ ₁ = inl (idp ₁)
```
